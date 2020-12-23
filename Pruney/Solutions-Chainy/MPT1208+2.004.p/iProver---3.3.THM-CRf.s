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
% DateTime   : Thu Dec  3 12:13:19 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :  249 (1515 expanded)
%              Number of clauses        :  161 ( 398 expanded)
%              Number of leaves         :   25 ( 377 expanded)
%              Depth                    :   19
%              Number of atoms          : 1233 (8407 expanded)
%              Number of equality atoms :  236 (1158 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f66,plain,(
    ! [X0] :
      ( v7_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f13,axiom,(
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

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f92,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f68,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v14_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( k4_lattices(X0,k6_lattices(X0),sK6) != sK6
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k4_lattices(X0,k6_lattices(X0),X1) != X1
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k4_lattices(sK5,k6_lattices(sK5),X1) != X1
          & m1_subset_1(X1,u1_struct_0(sK5)) )
      & l3_lattices(sK5)
      & v14_lattices(sK5)
      & v10_lattices(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( k4_lattices(sK5,k6_lattices(sK5),sK6) != sK6
    & m1_subset_1(sK6,u1_struct_0(sK5))
    & l3_lattices(sK5)
    & v14_lattices(sK5)
    & v10_lattices(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f43,f61,f60])).

fof(f94,plain,(
    v10_lattices(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f93,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f96,plain,(
    l3_lattices(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f11,axiom,(
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

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k2_lattices(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f7,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f84,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f82,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f97,plain,(
    m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f62])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f53,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f53])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,k1_lattices(X0,X1,sK4(X0))) != X1
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,sK3(X0),k1_lattices(X0,sK3(X0),X2)) != sK3(X0)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( k2_lattices(X0,sK3(X0),k1_lattices(X0,sK3(X0),sK4(X0))) != sK3(X0)
            & m1_subset_1(sK4(X0),u1_struct_0(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f54,f56,f55])).

fof(f77,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v14_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k6_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k1_lattices(X0,X2,X1) = X1
                    & k1_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k6_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k6_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ? [X2] :
                  ( ( k1_lattices(X0,X2,X1) != X1
                    | k1_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ( k1_lattices(X0,X2,X1) = X1
                    & k1_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ? [X2] :
                  ( ( k1_lattices(X0,X2,X1) != X1
                    | k1_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k1_lattices(X0,X3,X1) = X1
                    & k1_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k1_lattices(X0,X2,X1) != X1
            | k1_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k1_lattices(X0,sK0(X0,X1),X1) != X1
          | k1_lattices(X0,X1,sK0(X0,X1)) != X1 )
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ( ( k1_lattices(X0,sK0(X0,X1),X1) != X1
                  | k1_lattices(X0,X1,sK0(X0,X1)) != X1 )
                & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k1_lattices(X0,X3,X1) = X1
                    & k1_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( k1_lattices(X0,X3,X1) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k6_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f99,plain,(
    ! [X0,X3] :
      ( k6_lattices(X0) = k1_lattices(X0,X3,k6_lattices(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f95,plain,(
    v14_lattices(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f48])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k1_lattices(X0,k2_lattices(X0,X1,sK2(X0)),sK2(X0)) != sK2(X0)
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK1(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( k1_lattices(X0,k2_lattices(X0,sK1(X0),sK2(X0)),sK2(X0)) != sK2(X0)
            & m1_subset_1(sK2(X0),u1_struct_0(X0))
            & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f49,f51,f50])).

fof(f73,plain,(
    ! [X4,X0,X3] :
      ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f83,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,axiom,(
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

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_lattices(X0,X2,X1)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f10,axiom,(
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

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f58])).

fof(f98,plain,(
    k4_lattices(sK5,k6_lattices(sK5),sK6) != sK6 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1154,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_4214,plain,
    ( X0_54 != X1_54
    | X0_54 = k1_lattices(sK5,X2_54,X3_54)
    | k1_lattices(sK5,X2_54,X3_54) != X1_54 ),
    inference(instantiation,[status(thm)],[c_1154])).

cnf(c_12832,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),sK6) != X0_54
    | sK6 != X0_54
    | sK6 = k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_4214])).

cnf(c_12833,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),sK6) != sK6
    | sK6 = k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_12832])).

cnf(c_1159,plain,
    ( ~ r1_lattices(X0_56,X0_54,X1_54)
    | r1_lattices(X0_56,X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_3329,plain,
    ( ~ r1_lattices(sK5,X0_54,X1_54)
    | r1_lattices(sK5,X2_54,k4_lattices(sK5,k6_lattices(sK5),sK6))
    | X2_54 != X0_54
    | k4_lattices(sK5,k6_lattices(sK5),sK6) != X1_54 ),
    inference(instantiation,[status(thm)],[c_1159])).

cnf(c_6952,plain,
    ( r1_lattices(sK5,X0_54,k4_lattices(sK5,k6_lattices(sK5),sK6))
    | ~ r1_lattices(sK5,X1_54,k2_lattices(sK5,k6_lattices(sK5),sK6))
    | X0_54 != X1_54
    | k4_lattices(sK5,k6_lattices(sK5),sK6) != k2_lattices(sK5,k6_lattices(sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_3329])).

cnf(c_9859,plain,
    ( r1_lattices(sK5,X0_54,k4_lattices(sK5,k6_lattices(sK5),sK6))
    | ~ r1_lattices(sK5,k2_lattices(sK5,X1_54,sK6),k2_lattices(sK5,k6_lattices(sK5),sK6))
    | X0_54 != k2_lattices(sK5,X1_54,sK6)
    | k4_lattices(sK5,k6_lattices(sK5),sK6) != k2_lattices(sK5,k6_lattices(sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_6952])).

cnf(c_9861,plain,
    ( ~ r1_lattices(sK5,k2_lattices(sK5,sK6,sK6),k2_lattices(sK5,k6_lattices(sK5),sK6))
    | r1_lattices(sK5,sK6,k4_lattices(sK5,k6_lattices(sK5),sK6))
    | k4_lattices(sK5,k6_lattices(sK5),sK6) != k2_lattices(sK5,k6_lattices(sK5),sK6)
    | sK6 != k2_lattices(sK5,sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_9859])).

cnf(c_1644,plain,
    ( ~ r1_lattices(sK5,X0_54,X1_54)
    | r1_lattices(sK5,k4_lattices(sK5,k6_lattices(sK5),sK6),sK6)
    | k4_lattices(sK5,k6_lattices(sK5),sK6) != X0_54
    | sK6 != X1_54 ),
    inference(instantiation,[status(thm)],[c_1159])).

cnf(c_1702,plain,
    ( r1_lattices(sK5,k4_lattices(sK5,k6_lattices(sK5),sK6),sK6)
    | ~ r1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),X0_54)
    | k4_lattices(sK5,k6_lattices(sK5),sK6) != k2_lattices(sK5,k6_lattices(sK5),sK6)
    | sK6 != X0_54 ),
    inference(instantiation,[status(thm)],[c_1644])).

cnf(c_5793,plain,
    ( r1_lattices(sK5,k4_lattices(sK5,k6_lattices(sK5),sK6),sK6)
    | ~ r1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),sK6))
    | k4_lattices(sK5,k6_lattices(sK5),sK6) != k2_lattices(sK5,k6_lattices(sK5),sK6)
    | sK6 != k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_1702])).

cnf(c_1156,plain,
    ( ~ m1_subset_1(X0_54,X0_55)
    | m1_subset_1(X1_54,X0_55)
    | X1_54 != X0_54 ),
    theory(equality)).

cnf(c_1621,plain,
    ( m1_subset_1(X0_54,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | X0_54 != sK6 ),
    inference(instantiation,[status(thm)],[c_1156])).

cnf(c_2341,plain,
    ( m1_subset_1(k1_lattices(sK5,X0_54,X1_54),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | k1_lattices(sK5,X0_54,X1_54) != sK6 ),
    inference(instantiation,[status(thm)],[c_1621])).

cnf(c_3042,plain,
    ( m1_subset_1(k1_lattices(sK5,k2_lattices(sK5,X0_54,sK6),sK6),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | k1_lattices(sK5,k2_lattices(sK5,X0_54,sK6),sK6) != sK6 ),
    inference(instantiation,[status(thm)],[c_2341])).

cnf(c_4434,plain,
    ( m1_subset_1(k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),sK6),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),sK6) != sK6 ),
    inference(instantiation,[status(thm)],[c_3042])).

cnf(c_2,plain,
    ( v7_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_29,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_487,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | ~ v9_lattices(X0) ),
    inference(resolution,[status(thm)],[c_2,c_29])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_491,plain,
    ( ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | ~ r1_lattices(X0,X1,X2)
    | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_487,c_29,c_2,c_1,c_0])).

cnf(c_492,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(renaming,[status(thm)],[c_491])).

cnf(c_34,negated_conjecture,
    ( v10_lattices(sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_645,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_492,c_34])).

cnf(c_646,plain,
    ( ~ r1_lattices(sK5,X0,X1)
    | r1_lattices(sK5,k2_lattices(sK5,X0,X2),k2_lattices(sK5,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_645])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_32,negated_conjecture,
    ( l3_lattices(sK5) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_650,plain,
    ( ~ r1_lattices(sK5,X0,X1)
    | r1_lattices(sK5,k2_lattices(sK5,X0,X2),k2_lattices(sK5,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_646,c_35,c_32])).

cnf(c_651,plain,
    ( ~ r1_lattices(sK5,X0,X1)
    | r1_lattices(sK5,k2_lattices(sK5,X0,X2),k2_lattices(sK5,X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_650])).

cnf(c_1142,plain,
    ( ~ r1_lattices(sK5,X0_54,X1_54)
    | r1_lattices(sK5,k2_lattices(sK5,X0_54,X2_54),k2_lattices(sK5,X1_54,X2_54))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK5))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_651])).

cnf(c_2898,plain,
    ( ~ r1_lattices(sK5,X0_54,k6_lattices(sK5))
    | r1_lattices(sK5,k2_lattices(sK5,X0_54,sK6),k2_lattices(sK5,k6_lattices(sK5),sK6))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | ~ m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_1142])).

cnf(c_2904,plain,
    ( r1_lattices(sK5,k2_lattices(sK5,sK6,sK6),k2_lattices(sK5,k6_lattices(sK5),sK6))
    | ~ r1_lattices(sK5,sK6,k6_lattices(sK5))
    | ~ m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_2898])).

cnf(c_26,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) != X1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_911,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_35])).

cnf(c_912,plain,
    ( r1_lattices(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ v8_lattices(sK5)
    | ~ l3_lattices(sK5)
    | ~ v9_lattices(sK5)
    | k2_lattices(sK5,X0,X1) != X0 ),
    inference(unflattening,[status(thm)],[c_911])).

cnf(c_124,plain,
    ( v8_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_127,plain,
    ( ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5)
    | v9_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_914,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r1_lattices(sK5,X0,X1)
    | k2_lattices(sK5,X0,X1) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_912,c_35,c_34,c_32,c_124,c_127])).

cnf(c_915,plain,
    ( r1_lattices(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k2_lattices(sK5,X0,X1) != X0 ),
    inference(renaming,[status(thm)],[c_914])).

cnf(c_1136,plain,
    ( r1_lattices(sK5,X0_54,X1_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK5))
    | k2_lattices(sK5,X0_54,X1_54) != X0_54 ),
    inference(subtyping,[status(esa)],[c_915])).

cnf(c_1823,plain,
    ( r1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | ~ m1_subset_1(k2_lattices(sK5,k6_lattices(sK5),sK6),u1_struct_0(sK5))
    | k2_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),X0_54) != k2_lattices(sK5,k6_lattices(sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_1136])).

cnf(c_2863,plain,
    ( r1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),X0_54))
    | ~ m1_subset_1(k2_lattices(sK5,k6_lattices(sK5),sK6),u1_struct_0(sK5))
    | ~ m1_subset_1(k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),X0_54),u1_struct_0(sK5))
    | k2_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),X0_54)) != k2_lattices(sK5,k6_lattices(sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_1823])).

cnf(c_2865,plain,
    ( r1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),sK6))
    | ~ m1_subset_1(k2_lattices(sK5,k6_lattices(sK5),sK6),u1_struct_0(sK5))
    | ~ m1_subset_1(k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),sK6),u1_struct_0(sK5))
    | k2_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),sK6)) != k2_lattices(sK5,k6_lattices(sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_2863])).

cnf(c_20,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_19,plain,
    ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_627,plain,
    ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_20,c_19])).

cnf(c_876,plain,
    ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_627,c_35])).

cnf(c_877,plain,
    ( m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5))
    | ~ l3_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_876])).

cnf(c_69,plain,
    ( l2_lattices(sK5)
    | ~ l3_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_72,plain,
    ( m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5))
    | ~ l2_lattices(sK5)
    | v2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_879,plain,
    ( m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_877,c_35,c_32,c_69,c_72])).

cnf(c_1138,plain,
    ( m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_879])).

cnf(c_1472,plain,
    ( m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1138])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1147,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1461,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1147])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | k2_lattices(X1,X0,k1_lattices(X1,X0,X2)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_964,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v9_lattices(X1)
    | k2_lattices(X1,X0,k1_lattices(X1,X0,X2)) = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_35])).

cnf(c_965,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | ~ v9_lattices(sK5)
    | k2_lattices(sK5,X0,k1_lattices(sK5,X0,X1)) = X0 ),
    inference(unflattening,[status(thm)],[c_964])).

cnf(c_969,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k2_lattices(sK5,X0,k1_lattices(sK5,X0,X1)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_965,c_35,c_34,c_32,c_127])).

cnf(c_1134,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK5))
    | k2_lattices(sK5,X0_54,k1_lattices(sK5,X0_54,X1_54)) = X0_54 ),
    inference(subtyping,[status(esa)],[c_969])).

cnf(c_1476,plain,
    ( k2_lattices(sK5,X0_54,k1_lattices(sK5,X0_54,X1_54)) = X0_54
    | m1_subset_1(X0_54,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1134])).

cnf(c_1885,plain,
    ( k2_lattices(sK5,sK6,k1_lattices(sK5,sK6,X0_54)) = sK6
    | m1_subset_1(X0_54,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1461,c_1476])).

cnf(c_2073,plain,
    ( k2_lattices(sK5,sK6,k1_lattices(sK5,sK6,k6_lattices(sK5))) = sK6 ),
    inference(superposition,[status(thm)],[c_1472,c_1885])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v14_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X0,k6_lattices(X1)) = k6_lattices(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_33,negated_conjecture,
    ( v14_lattices(sK5) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_549,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X0,k6_lattices(X1)) = k6_lattices(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_33])).

cnf(c_550,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5))
    | ~ l2_lattices(sK5)
    | v2_struct_0(sK5)
    | k1_lattices(sK5,X0,k6_lattices(sK5)) = k6_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_549])).

cnf(c_554,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k1_lattices(sK5,X0,k6_lattices(sK5)) = k6_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_550,c_35,c_32,c_69,c_72])).

cnf(c_1145,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | k1_lattices(sK5,X0_54,k6_lattices(sK5)) = k6_lattices(sK5) ),
    inference(subtyping,[status(esa)],[c_554])).

cnf(c_1463,plain,
    ( k1_lattices(sK5,X0_54,k6_lattices(sK5)) = k6_lattices(sK5)
    | m1_subset_1(X0_54,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1145])).

cnf(c_1670,plain,
    ( k1_lattices(sK5,sK6,k6_lattices(sK5)) = k6_lattices(sK5) ),
    inference(superposition,[status(thm)],[c_1461,c_1463])).

cnf(c_2089,plain,
    ( k2_lattices(sK5,sK6,k6_lattices(sK5)) = sK6 ),
    inference(light_normalisation,[status(thm)],[c_2073,c_1670])).

cnf(c_1474,plain,
    ( k2_lattices(sK5,X0_54,X1_54) != X0_54
    | r1_lattices(sK5,X0_54,X1_54) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1136])).

cnf(c_2405,plain,
    ( r1_lattices(sK5,sK6,k6_lattices(sK5)) = iProver_top
    | m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2089,c_1474])).

cnf(c_2419,plain,
    ( r1_lattices(sK5,sK6,k6_lattices(sK5))
    | ~ m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2405])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X0,X2),X2) = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_985,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | k1_lattices(X1,k2_lattices(X1,X0,X2),X2) = X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_35])).

cnf(c_986,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ v8_lattices(sK5)
    | ~ l3_lattices(sK5)
    | k1_lattices(sK5,k2_lattices(sK5,X0,X1),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_985])).

cnf(c_990,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k1_lattices(sK5,k2_lattices(sK5,X0,X1),X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_986,c_35,c_34,c_32,c_124])).

cnf(c_1133,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK5))
    | k1_lattices(sK5,k2_lattices(sK5,X0_54,X1_54),X1_54) = X1_54 ),
    inference(subtyping,[status(esa)],[c_990])).

cnf(c_1477,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,X0_54,X1_54),X1_54) = X1_54
    | m1_subset_1(X0_54,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1133])).

cnf(c_2150,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),X0_54),X0_54) = X0_54
    | m1_subset_1(X0_54,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1472,c_1477])).

cnf(c_2179,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),sK6) = sK6
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2150])).

cnf(c_2064,plain,
    ( k2_lattices(sK5,X0_54,sK6) != X1_54
    | sK6 != X1_54
    | sK6 = k2_lattices(sK5,X0_54,sK6) ),
    inference(instantiation,[status(thm)],[c_1154])).

cnf(c_2065,plain,
    ( k2_lattices(sK5,sK6,sK6) != sK6
    | sK6 = k2_lattices(sK5,sK6,sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2064])).

cnf(c_21,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k2_lattices(X1,X0,X2),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_453,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k2_lattices(X1,X0,X2),u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_18])).

cnf(c_454,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k2_lattices(X1,X0,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_943,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k2_lattices(X1,X0,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_454,c_35])).

cnf(c_944,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(k2_lattices(sK5,X0,X1),u1_struct_0(sK5))
    | ~ l3_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_943])).

cnf(c_948,plain,
    ( m1_subset_1(k2_lattices(sK5,X0,X1),u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_944,c_32])).

cnf(c_949,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(k2_lattices(sK5,X0,X1),u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_948])).

cnf(c_1135,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK5))
    | m1_subset_1(k2_lattices(sK5,X0_54,X1_54),u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_949])).

cnf(c_2033,plain,
    ( m1_subset_1(k2_lattices(sK5,k6_lattices(sK5),sK6),u1_struct_0(sK5))
    | ~ m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_1135])).

cnf(c_1627,plain,
    ( m1_subset_1(X0_54,u1_struct_0(sK5))
    | ~ m1_subset_1(k2_lattices(sK5,X1_54,X2_54),u1_struct_0(sK5))
    | X0_54 != k2_lattices(sK5,X1_54,X2_54) ),
    inference(instantiation,[status(thm)],[c_1156])).

cnf(c_1674,plain,
    ( m1_subset_1(k4_lattices(sK5,k6_lattices(sK5),sK6),u1_struct_0(sK5))
    | ~ m1_subset_1(k2_lattices(sK5,X0_54,X1_54),u1_struct_0(sK5))
    | k4_lattices(sK5,k6_lattices(sK5),sK6) != k2_lattices(sK5,X0_54,X1_54) ),
    inference(instantiation,[status(thm)],[c_1627])).

cnf(c_1988,plain,
    ( m1_subset_1(k4_lattices(sK5,k6_lattices(sK5),sK6),u1_struct_0(sK5))
    | ~ m1_subset_1(k2_lattices(sK5,k6_lattices(sK5),sK6),u1_struct_0(sK5))
    | k4_lattices(sK5,k6_lattices(sK5),sK6) != k2_lattices(sK5,k6_lattices(sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_1674])).

cnf(c_1931,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | ~ m1_subset_1(k2_lattices(sK5,k6_lattices(sK5),sK6),u1_struct_0(sK5))
    | k2_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),X0_54)) = k2_lattices(sK5,k6_lattices(sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_1134])).

cnf(c_1934,plain,
    ( ~ m1_subset_1(k2_lattices(sK5,k6_lattices(sK5),sK6),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | k2_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),sK6)) = k2_lattices(sK5,k6_lattices(sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_1931])).

cnf(c_4,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_28,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | ~ v4_lattices(X0)
    | v2_struct_0(X0)
    | X2 = X1 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_385,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | X2 = X1 ),
    inference(resolution,[status(thm)],[c_4,c_28])).

cnf(c_389,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r1_lattices(X0,X2,X1)
    | ~ r1_lattices(X0,X1,X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | X2 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_385,c_20])).

cnf(c_390,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | X2 = X1 ),
    inference(renaming,[status(thm)],[c_389])).

cnf(c_672,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | X2 = X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_390,c_34])).

cnf(c_673,plain,
    ( ~ r1_lattices(sK5,X0,X1)
    | ~ r1_lattices(sK5,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_672])).

cnf(c_677,plain,
    ( ~ r1_lattices(sK5,X0,X1)
    | ~ r1_lattices(sK5,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_673,c_35,c_32])).

cnf(c_678,plain,
    ( ~ r1_lattices(sK5,X0,X1)
    | ~ r1_lattices(sK5,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_677])).

cnf(c_1141,plain,
    ( ~ r1_lattices(sK5,X0_54,X1_54)
    | ~ r1_lattices(sK5,X1_54,X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK5))
    | X1_54 = X0_54 ),
    inference(subtyping,[status(esa)],[c_678])).

cnf(c_1689,plain,
    ( ~ r1_lattices(sK5,k4_lattices(sK5,k6_lattices(sK5),sK6),sK6)
    | ~ r1_lattices(sK5,sK6,k4_lattices(sK5,k6_lattices(sK5),sK6))
    | ~ m1_subset_1(k4_lattices(sK5,k6_lattices(sK5),sK6),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | sK6 = k4_lattices(sK5,k6_lattices(sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_1141])).

cnf(c_1153,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_1655,plain,
    ( k4_lattices(sK5,k6_lattices(sK5),sK6) = k4_lattices(sK5,k6_lattices(sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_1153])).

cnf(c_1620,plain,
    ( k4_lattices(sK5,k6_lattices(sK5),sK6) != X0_54
    | k4_lattices(sK5,k6_lattices(sK5),sK6) = sK6
    | sK6 != X0_54 ),
    inference(instantiation,[status(thm)],[c_1154])).

cnf(c_1654,plain,
    ( k4_lattices(sK5,k6_lattices(sK5),sK6) != k4_lattices(sK5,k6_lattices(sK5),sK6)
    | k4_lattices(sK5,k6_lattices(sK5),sK6) = sK6
    | sK6 != k4_lattices(sK5,k6_lattices(sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_1620])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_429,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2) ),
    inference(resolution_lifted,[status(thm)],[c_21,c_22])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_3,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_699,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_34])).

cnf(c_700,plain,
    ( v6_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_699])).

cnf(c_118,plain,
    ( v6_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_702,plain,
    ( v6_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_700,c_35,c_34,c_32,c_118])).

cnf(c_817,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_430,c_702])).

cnf(c_818,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | k4_lattices(sK5,X0,X1) = k2_lattices(sK5,X0,X1) ),
    inference(unflattening,[status(thm)],[c_817])).

cnf(c_822,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k4_lattices(sK5,X0,X1) = k2_lattices(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_818,c_35,c_32])).

cnf(c_1140,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK5))
    | k4_lattices(sK5,X0_54,X1_54) = k2_lattices(sK5,X0_54,X1_54) ),
    inference(subtyping,[status(esa)],[c_822])).

cnf(c_1648,plain,
    ( ~ m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | k4_lattices(sK5,k6_lattices(sK5),sK6) = k2_lattices(sK5,k6_lattices(sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_1140])).

cnf(c_27,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_887,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_35])).

cnf(c_888,plain,
    ( ~ r1_lattices(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ v8_lattices(sK5)
    | ~ l3_lattices(sK5)
    | ~ v9_lattices(sK5)
    | k2_lattices(sK5,X0,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_887])).

cnf(c_892,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r1_lattices(sK5,X0,X1)
    | k2_lattices(sK5,X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_888,c_35,c_34,c_32,c_124,c_127])).

cnf(c_893,plain,
    ( ~ r1_lattices(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k2_lattices(sK5,X0,X1) = X0 ),
    inference(renaming,[status(thm)],[c_892])).

cnf(c_1137,plain,
    ( ~ r1_lattices(sK5,X0_54,X1_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK5))
    | k2_lattices(sK5,X0_54,X1_54) = X0_54 ),
    inference(subtyping,[status(esa)],[c_893])).

cnf(c_1196,plain,
    ( ~ r1_lattices(sK5,sK6,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | k2_lattices(sK5,sK6,sK6) = sK6 ),
    inference(instantiation,[status(thm)],[c_1137])).

cnf(c_25,plain,
    ( r3_lattices(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_750,plain,
    ( r3_lattices(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_702])).

cnf(c_751,plain,
    ( r3_lattices(sK5,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ v8_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v9_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_750])).

cnf(c_755,plain,
    ( r3_lattices(sK5,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_751,c_35,c_34,c_32,c_124,c_127])).

cnf(c_756,plain,
    ( r3_lattices(sK5,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_755])).

cnf(c_24,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_771,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_702])).

cnf(c_772,plain,
    ( r1_lattices(sK5,X0,X1)
    | ~ r3_lattices(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ v8_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v9_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_771])).

cnf(c_776,plain,
    ( r1_lattices(sK5,X0,X1)
    | ~ r3_lattices(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_772,c_35,c_34,c_32,c_124,c_127])).

cnf(c_777,plain,
    ( r1_lattices(sK5,X0,X1)
    | ~ r3_lattices(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_776])).

cnf(c_857,plain,
    ( r1_lattices(sK5,X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X3,u1_struct_0(sK5))
    | X0 != X2
    | X1 != X2
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_756,c_777])).

cnf(c_858,plain,
    ( r1_lattices(sK5,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_857])).

cnf(c_1139,plain,
    ( r1_lattices(sK5,X0_54,X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_858])).

cnf(c_1149,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1139])).

cnf(c_1192,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_1149])).

cnf(c_1150,plain,
    ( r1_lattices(sK5,X0_54,X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_1139])).

cnf(c_1189,plain,
    ( r1_lattices(sK5,sK6,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ sP1_iProver_split ),
    inference(instantiation,[status(thm)],[c_1150])).

cnf(c_1151,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1139])).

cnf(c_30,negated_conjecture,
    ( k4_lattices(sK5,k6_lattices(sK5),sK6) != sK6 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1148,negated_conjecture,
    ( k4_lattices(sK5,k6_lattices(sK5),sK6) != sK6 ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1166,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1153])).

cnf(c_40,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12833,c_9861,c_5793,c_4434,c_2904,c_2865,c_2419,c_2179,c_2065,c_2033,c_1988,c_1934,c_1689,c_1655,c_1654,c_1648,c_1196,c_1192,c_1189,c_1151,c_1148,c_1166,c_72,c_69,c_40,c_31,c_32,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:38:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.71/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.04  
% 1.71/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.71/1.04  
% 1.71/1.04  ------  iProver source info
% 1.71/1.04  
% 1.71/1.04  git: date: 2020-06-30 10:37:57 +0100
% 1.71/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.71/1.04  git: non_committed_changes: false
% 1.71/1.04  git: last_make_outside_of_git: false
% 1.71/1.04  
% 1.71/1.04  ------ 
% 1.71/1.04  
% 1.71/1.04  ------ Input Options
% 1.71/1.04  
% 1.71/1.04  --out_options                           all
% 1.71/1.04  --tptp_safe_out                         true
% 1.71/1.04  --problem_path                          ""
% 1.71/1.04  --include_path                          ""
% 1.71/1.04  --clausifier                            res/vclausify_rel
% 1.71/1.04  --clausifier_options                    --mode clausify
% 1.71/1.04  --stdin                                 false
% 1.71/1.04  --stats_out                             all
% 1.71/1.04  
% 1.71/1.04  ------ General Options
% 1.71/1.04  
% 1.71/1.04  --fof                                   false
% 1.71/1.04  --time_out_real                         305.
% 1.71/1.04  --time_out_virtual                      -1.
% 1.71/1.04  --symbol_type_check                     false
% 1.71/1.04  --clausify_out                          false
% 1.71/1.04  --sig_cnt_out                           false
% 1.71/1.04  --trig_cnt_out                          false
% 1.71/1.04  --trig_cnt_out_tolerance                1.
% 1.71/1.04  --trig_cnt_out_sk_spl                   false
% 1.71/1.04  --abstr_cl_out                          false
% 1.71/1.04  
% 1.71/1.04  ------ Global Options
% 1.71/1.04  
% 1.71/1.04  --schedule                              default
% 1.71/1.04  --add_important_lit                     false
% 1.71/1.04  --prop_solver_per_cl                    1000
% 1.71/1.04  --min_unsat_core                        false
% 1.71/1.04  --soft_assumptions                      false
% 1.71/1.04  --soft_lemma_size                       3
% 1.71/1.04  --prop_impl_unit_size                   0
% 1.71/1.04  --prop_impl_unit                        []
% 1.71/1.04  --share_sel_clauses                     true
% 1.71/1.04  --reset_solvers                         false
% 1.71/1.04  --bc_imp_inh                            [conj_cone]
% 1.71/1.04  --conj_cone_tolerance                   3.
% 1.71/1.04  --extra_neg_conj                        none
% 1.71/1.04  --large_theory_mode                     true
% 1.71/1.04  --prolific_symb_bound                   200
% 1.71/1.04  --lt_threshold                          2000
% 1.71/1.04  --clause_weak_htbl                      true
% 1.71/1.04  --gc_record_bc_elim                     false
% 1.71/1.04  
% 1.71/1.04  ------ Preprocessing Options
% 1.71/1.04  
% 1.71/1.04  --preprocessing_flag                    true
% 1.71/1.04  --time_out_prep_mult                    0.1
% 1.71/1.04  --splitting_mode                        input
% 1.71/1.04  --splitting_grd                         true
% 1.71/1.04  --splitting_cvd                         false
% 1.71/1.04  --splitting_cvd_svl                     false
% 1.71/1.04  --splitting_nvd                         32
% 1.71/1.04  --sub_typing                            true
% 1.71/1.04  --prep_gs_sim                           true
% 1.71/1.04  --prep_unflatten                        true
% 1.71/1.04  --prep_res_sim                          true
% 1.71/1.04  --prep_upred                            true
% 1.71/1.04  --prep_sem_filter                       exhaustive
% 1.71/1.04  --prep_sem_filter_out                   false
% 1.71/1.04  --pred_elim                             true
% 1.71/1.04  --res_sim_input                         true
% 1.71/1.04  --eq_ax_congr_red                       true
% 1.71/1.04  --pure_diseq_elim                       true
% 1.71/1.04  --brand_transform                       false
% 1.71/1.04  --non_eq_to_eq                          false
% 1.71/1.04  --prep_def_merge                        true
% 1.71/1.04  --prep_def_merge_prop_impl              false
% 1.71/1.04  --prep_def_merge_mbd                    true
% 1.71/1.04  --prep_def_merge_tr_red                 false
% 1.71/1.04  --prep_def_merge_tr_cl                  false
% 1.71/1.04  --smt_preprocessing                     true
% 1.71/1.04  --smt_ac_axioms                         fast
% 1.71/1.04  --preprocessed_out                      false
% 1.71/1.04  --preprocessed_stats                    false
% 1.71/1.04  
% 1.71/1.04  ------ Abstraction refinement Options
% 1.71/1.04  
% 1.71/1.04  --abstr_ref                             []
% 1.71/1.04  --abstr_ref_prep                        false
% 1.71/1.04  --abstr_ref_until_sat                   false
% 1.71/1.04  --abstr_ref_sig_restrict                funpre
% 1.71/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 1.71/1.04  --abstr_ref_under                       []
% 1.71/1.04  
% 1.71/1.04  ------ SAT Options
% 1.71/1.04  
% 1.71/1.04  --sat_mode                              false
% 1.71/1.04  --sat_fm_restart_options                ""
% 1.71/1.04  --sat_gr_def                            false
% 1.71/1.04  --sat_epr_types                         true
% 1.71/1.04  --sat_non_cyclic_types                  false
% 1.71/1.04  --sat_finite_models                     false
% 1.71/1.04  --sat_fm_lemmas                         false
% 1.71/1.04  --sat_fm_prep                           false
% 1.71/1.04  --sat_fm_uc_incr                        true
% 1.71/1.04  --sat_out_model                         small
% 1.71/1.04  --sat_out_clauses                       false
% 1.71/1.04  
% 1.71/1.04  ------ QBF Options
% 1.71/1.04  
% 1.71/1.04  --qbf_mode                              false
% 1.71/1.04  --qbf_elim_univ                         false
% 1.71/1.04  --qbf_dom_inst                          none
% 1.71/1.04  --qbf_dom_pre_inst                      false
% 1.71/1.04  --qbf_sk_in                             false
% 1.71/1.04  --qbf_pred_elim                         true
% 1.71/1.04  --qbf_split                             512
% 1.71/1.04  
% 1.71/1.04  ------ BMC1 Options
% 1.71/1.04  
% 1.71/1.04  --bmc1_incremental                      false
% 1.71/1.04  --bmc1_axioms                           reachable_all
% 1.71/1.04  --bmc1_min_bound                        0
% 1.71/1.04  --bmc1_max_bound                        -1
% 1.71/1.04  --bmc1_max_bound_default                -1
% 1.71/1.04  --bmc1_symbol_reachability              true
% 1.71/1.04  --bmc1_property_lemmas                  false
% 1.71/1.04  --bmc1_k_induction                      false
% 1.71/1.04  --bmc1_non_equiv_states                 false
% 1.71/1.04  --bmc1_deadlock                         false
% 1.71/1.04  --bmc1_ucm                              false
% 1.71/1.04  --bmc1_add_unsat_core                   none
% 1.71/1.04  --bmc1_unsat_core_children              false
% 1.71/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 1.71/1.04  --bmc1_out_stat                         full
% 1.71/1.04  --bmc1_ground_init                      false
% 1.71/1.04  --bmc1_pre_inst_next_state              false
% 1.71/1.04  --bmc1_pre_inst_state                   false
% 1.71/1.04  --bmc1_pre_inst_reach_state             false
% 1.71/1.04  --bmc1_out_unsat_core                   false
% 1.71/1.04  --bmc1_aig_witness_out                  false
% 1.71/1.04  --bmc1_verbose                          false
% 1.71/1.04  --bmc1_dump_clauses_tptp                false
% 1.71/1.04  --bmc1_dump_unsat_core_tptp             false
% 1.71/1.04  --bmc1_dump_file                        -
% 1.71/1.04  --bmc1_ucm_expand_uc_limit              128
% 1.71/1.04  --bmc1_ucm_n_expand_iterations          6
% 1.71/1.04  --bmc1_ucm_extend_mode                  1
% 1.71/1.04  --bmc1_ucm_init_mode                    2
% 1.71/1.04  --bmc1_ucm_cone_mode                    none
% 1.71/1.04  --bmc1_ucm_reduced_relation_type        0
% 1.71/1.04  --bmc1_ucm_relax_model                  4
% 1.71/1.04  --bmc1_ucm_full_tr_after_sat            true
% 1.71/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 1.71/1.04  --bmc1_ucm_layered_model                none
% 1.71/1.04  --bmc1_ucm_max_lemma_size               10
% 1.71/1.04  
% 1.71/1.04  ------ AIG Options
% 1.71/1.04  
% 1.71/1.04  --aig_mode                              false
% 1.71/1.04  
% 1.71/1.04  ------ Instantiation Options
% 1.71/1.04  
% 1.71/1.04  --instantiation_flag                    true
% 1.71/1.04  --inst_sos_flag                         false
% 1.71/1.04  --inst_sos_phase                        true
% 1.71/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.71/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.71/1.04  --inst_lit_sel_side                     num_symb
% 1.71/1.04  --inst_solver_per_active                1400
% 1.71/1.04  --inst_solver_calls_frac                1.
% 1.71/1.04  --inst_passive_queue_type               priority_queues
% 1.71/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.71/1.04  --inst_passive_queues_freq              [25;2]
% 1.71/1.04  --inst_dismatching                      true
% 1.71/1.04  --inst_eager_unprocessed_to_passive     true
% 1.71/1.04  --inst_prop_sim_given                   true
% 1.71/1.04  --inst_prop_sim_new                     false
% 1.71/1.04  --inst_subs_new                         false
% 1.71/1.04  --inst_eq_res_simp                      false
% 1.71/1.04  --inst_subs_given                       false
% 1.71/1.04  --inst_orphan_elimination               true
% 1.71/1.04  --inst_learning_loop_flag               true
% 1.71/1.04  --inst_learning_start                   3000
% 1.71/1.04  --inst_learning_factor                  2
% 1.71/1.04  --inst_start_prop_sim_after_learn       3
% 1.71/1.04  --inst_sel_renew                        solver
% 1.71/1.04  --inst_lit_activity_flag                true
% 1.71/1.04  --inst_restr_to_given                   false
% 1.71/1.04  --inst_activity_threshold               500
% 1.71/1.04  --inst_out_proof                        true
% 1.71/1.04  
% 1.71/1.04  ------ Resolution Options
% 1.71/1.04  
% 1.71/1.04  --resolution_flag                       true
% 1.71/1.04  --res_lit_sel                           adaptive
% 1.71/1.04  --res_lit_sel_side                      none
% 1.71/1.04  --res_ordering                          kbo
% 1.71/1.04  --res_to_prop_solver                    active
% 1.71/1.04  --res_prop_simpl_new                    false
% 1.71/1.04  --res_prop_simpl_given                  true
% 1.71/1.04  --res_passive_queue_type                priority_queues
% 1.71/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.71/1.04  --res_passive_queues_freq               [15;5]
% 1.71/1.04  --res_forward_subs                      full
% 1.71/1.04  --res_backward_subs                     full
% 1.71/1.04  --res_forward_subs_resolution           true
% 1.71/1.04  --res_backward_subs_resolution          true
% 1.71/1.04  --res_orphan_elimination                true
% 1.71/1.04  --res_time_limit                        2.
% 1.71/1.04  --res_out_proof                         true
% 1.71/1.04  
% 1.71/1.04  ------ Superposition Options
% 1.71/1.04  
% 1.71/1.04  --superposition_flag                    true
% 1.71/1.04  --sup_passive_queue_type                priority_queues
% 1.71/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.71/1.04  --sup_passive_queues_freq               [8;1;4]
% 1.71/1.04  --demod_completeness_check              fast
% 1.71/1.04  --demod_use_ground                      true
% 1.71/1.04  --sup_to_prop_solver                    passive
% 1.71/1.04  --sup_prop_simpl_new                    true
% 1.71/1.04  --sup_prop_simpl_given                  true
% 1.71/1.04  --sup_fun_splitting                     false
% 1.71/1.04  --sup_smt_interval                      50000
% 1.71/1.04  
% 1.71/1.04  ------ Superposition Simplification Setup
% 1.71/1.04  
% 1.71/1.04  --sup_indices_passive                   []
% 1.71/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 1.71/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/1.04  --sup_full_bw                           [BwDemod]
% 1.71/1.04  --sup_immed_triv                        [TrivRules]
% 1.71/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.71/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/1.04  --sup_immed_bw_main                     []
% 1.71/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 1.71/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/1.04  
% 1.71/1.04  ------ Combination Options
% 1.71/1.04  
% 1.71/1.04  --comb_res_mult                         3
% 1.71/1.04  --comb_sup_mult                         2
% 1.71/1.04  --comb_inst_mult                        10
% 1.71/1.04  
% 1.71/1.04  ------ Debug Options
% 1.71/1.04  
% 1.71/1.04  --dbg_backtrace                         false
% 1.71/1.04  --dbg_dump_prop_clauses                 false
% 1.71/1.04  --dbg_dump_prop_clauses_file            -
% 1.71/1.04  --dbg_out_stat                          false
% 1.71/1.04  ------ Parsing...
% 1.71/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.71/1.04  
% 1.71/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.71/1.04  
% 1.71/1.04  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.71/1.04  
% 1.71/1.04  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.71/1.04  ------ Proving...
% 1.71/1.04  ------ Problem Properties 
% 1.71/1.04  
% 1.71/1.04  
% 1.71/1.04  clauses                                 18
% 1.71/1.04  conjectures                             2
% 1.71/1.04  EPR                                     1
% 1.71/1.04  Horn                                    16
% 1.71/1.04  unary                                   3
% 1.71/1.04  binary                                  4
% 1.71/1.04  lits                                    51
% 1.71/1.04  lits eq                                 13
% 1.71/1.04  fd_pure                                 0
% 1.71/1.04  fd_pseudo                               0
% 1.71/1.04  fd_cond                                 2
% 1.71/1.04  fd_pseudo_cond                          1
% 1.71/1.04  AC symbols                              0
% 1.71/1.04  
% 1.71/1.04  ------ Schedule dynamic 5 is on 
% 1.71/1.04  
% 1.71/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.71/1.04  
% 1.71/1.04  
% 1.71/1.04  ------ 
% 1.71/1.04  Current options:
% 1.71/1.04  ------ 
% 1.71/1.04  
% 1.71/1.04  ------ Input Options
% 1.71/1.04  
% 1.71/1.04  --out_options                           all
% 1.71/1.04  --tptp_safe_out                         true
% 1.71/1.04  --problem_path                          ""
% 1.71/1.04  --include_path                          ""
% 1.71/1.04  --clausifier                            res/vclausify_rel
% 1.71/1.04  --clausifier_options                    --mode clausify
% 1.71/1.04  --stdin                                 false
% 1.71/1.04  --stats_out                             all
% 1.71/1.04  
% 1.71/1.04  ------ General Options
% 1.71/1.04  
% 1.71/1.04  --fof                                   false
% 1.71/1.04  --time_out_real                         305.
% 1.71/1.04  --time_out_virtual                      -1.
% 1.71/1.04  --symbol_type_check                     false
% 1.71/1.04  --clausify_out                          false
% 1.71/1.04  --sig_cnt_out                           false
% 1.71/1.04  --trig_cnt_out                          false
% 1.71/1.04  --trig_cnt_out_tolerance                1.
% 1.71/1.04  --trig_cnt_out_sk_spl                   false
% 1.71/1.04  --abstr_cl_out                          false
% 1.71/1.04  
% 1.71/1.04  ------ Global Options
% 1.71/1.04  
% 1.71/1.04  --schedule                              default
% 1.71/1.04  --add_important_lit                     false
% 1.71/1.04  --prop_solver_per_cl                    1000
% 1.71/1.04  --min_unsat_core                        false
% 1.71/1.04  --soft_assumptions                      false
% 1.71/1.04  --soft_lemma_size                       3
% 1.71/1.04  --prop_impl_unit_size                   0
% 1.71/1.04  --prop_impl_unit                        []
% 1.71/1.04  --share_sel_clauses                     true
% 1.71/1.04  --reset_solvers                         false
% 1.71/1.04  --bc_imp_inh                            [conj_cone]
% 1.71/1.04  --conj_cone_tolerance                   3.
% 1.71/1.04  --extra_neg_conj                        none
% 1.71/1.04  --large_theory_mode                     true
% 1.71/1.04  --prolific_symb_bound                   200
% 1.71/1.04  --lt_threshold                          2000
% 1.71/1.04  --clause_weak_htbl                      true
% 1.71/1.04  --gc_record_bc_elim                     false
% 1.71/1.04  
% 1.71/1.04  ------ Preprocessing Options
% 1.71/1.04  
% 1.71/1.04  --preprocessing_flag                    true
% 1.71/1.04  --time_out_prep_mult                    0.1
% 1.71/1.04  --splitting_mode                        input
% 1.71/1.04  --splitting_grd                         true
% 1.71/1.04  --splitting_cvd                         false
% 1.71/1.04  --splitting_cvd_svl                     false
% 1.71/1.04  --splitting_nvd                         32
% 1.71/1.04  --sub_typing                            true
% 1.71/1.04  --prep_gs_sim                           true
% 1.71/1.04  --prep_unflatten                        true
% 1.71/1.04  --prep_res_sim                          true
% 1.71/1.04  --prep_upred                            true
% 1.71/1.04  --prep_sem_filter                       exhaustive
% 1.71/1.04  --prep_sem_filter_out                   false
% 1.71/1.04  --pred_elim                             true
% 1.71/1.04  --res_sim_input                         true
% 1.71/1.04  --eq_ax_congr_red                       true
% 1.71/1.04  --pure_diseq_elim                       true
% 1.71/1.04  --brand_transform                       false
% 1.71/1.04  --non_eq_to_eq                          false
% 1.71/1.04  --prep_def_merge                        true
% 1.71/1.04  --prep_def_merge_prop_impl              false
% 1.71/1.04  --prep_def_merge_mbd                    true
% 1.71/1.04  --prep_def_merge_tr_red                 false
% 1.71/1.04  --prep_def_merge_tr_cl                  false
% 1.71/1.04  --smt_preprocessing                     true
% 1.71/1.04  --smt_ac_axioms                         fast
% 1.71/1.04  --preprocessed_out                      false
% 1.71/1.04  --preprocessed_stats                    false
% 1.71/1.04  
% 1.71/1.04  ------ Abstraction refinement Options
% 1.71/1.04  
% 1.71/1.04  --abstr_ref                             []
% 1.71/1.04  --abstr_ref_prep                        false
% 1.71/1.04  --abstr_ref_until_sat                   false
% 1.71/1.04  --abstr_ref_sig_restrict                funpre
% 1.71/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 1.71/1.04  --abstr_ref_under                       []
% 1.71/1.04  
% 1.71/1.04  ------ SAT Options
% 1.71/1.04  
% 1.71/1.04  --sat_mode                              false
% 1.71/1.04  --sat_fm_restart_options                ""
% 1.71/1.04  --sat_gr_def                            false
% 1.71/1.04  --sat_epr_types                         true
% 1.71/1.04  --sat_non_cyclic_types                  false
% 1.71/1.04  --sat_finite_models                     false
% 1.71/1.04  --sat_fm_lemmas                         false
% 1.71/1.04  --sat_fm_prep                           false
% 1.71/1.04  --sat_fm_uc_incr                        true
% 1.71/1.04  --sat_out_model                         small
% 1.71/1.04  --sat_out_clauses                       false
% 1.71/1.04  
% 1.71/1.04  ------ QBF Options
% 1.71/1.04  
% 1.71/1.04  --qbf_mode                              false
% 1.71/1.04  --qbf_elim_univ                         false
% 1.71/1.04  --qbf_dom_inst                          none
% 1.71/1.04  --qbf_dom_pre_inst                      false
% 1.71/1.04  --qbf_sk_in                             false
% 1.71/1.04  --qbf_pred_elim                         true
% 1.71/1.04  --qbf_split                             512
% 1.71/1.04  
% 1.71/1.04  ------ BMC1 Options
% 1.71/1.04  
% 1.71/1.04  --bmc1_incremental                      false
% 1.71/1.04  --bmc1_axioms                           reachable_all
% 1.71/1.04  --bmc1_min_bound                        0
% 1.71/1.04  --bmc1_max_bound                        -1
% 1.71/1.04  --bmc1_max_bound_default                -1
% 1.71/1.04  --bmc1_symbol_reachability              true
% 1.71/1.04  --bmc1_property_lemmas                  false
% 1.71/1.04  --bmc1_k_induction                      false
% 1.71/1.04  --bmc1_non_equiv_states                 false
% 1.71/1.04  --bmc1_deadlock                         false
% 1.71/1.04  --bmc1_ucm                              false
% 1.71/1.04  --bmc1_add_unsat_core                   none
% 1.71/1.04  --bmc1_unsat_core_children              false
% 1.71/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 1.71/1.04  --bmc1_out_stat                         full
% 1.71/1.04  --bmc1_ground_init                      false
% 1.71/1.04  --bmc1_pre_inst_next_state              false
% 1.71/1.04  --bmc1_pre_inst_state                   false
% 1.71/1.04  --bmc1_pre_inst_reach_state             false
% 1.71/1.04  --bmc1_out_unsat_core                   false
% 1.71/1.04  --bmc1_aig_witness_out                  false
% 1.71/1.04  --bmc1_verbose                          false
% 1.71/1.04  --bmc1_dump_clauses_tptp                false
% 1.71/1.04  --bmc1_dump_unsat_core_tptp             false
% 1.71/1.04  --bmc1_dump_file                        -
% 1.71/1.04  --bmc1_ucm_expand_uc_limit              128
% 1.71/1.04  --bmc1_ucm_n_expand_iterations          6
% 1.71/1.04  --bmc1_ucm_extend_mode                  1
% 1.71/1.04  --bmc1_ucm_init_mode                    2
% 1.71/1.04  --bmc1_ucm_cone_mode                    none
% 1.71/1.04  --bmc1_ucm_reduced_relation_type        0
% 1.71/1.04  --bmc1_ucm_relax_model                  4
% 1.71/1.04  --bmc1_ucm_full_tr_after_sat            true
% 1.71/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 1.71/1.04  --bmc1_ucm_layered_model                none
% 1.71/1.04  --bmc1_ucm_max_lemma_size               10
% 1.71/1.04  
% 1.71/1.04  ------ AIG Options
% 1.71/1.04  
% 1.71/1.04  --aig_mode                              false
% 1.71/1.04  
% 1.71/1.04  ------ Instantiation Options
% 1.71/1.04  
% 1.71/1.04  --instantiation_flag                    true
% 1.71/1.04  --inst_sos_flag                         false
% 1.71/1.04  --inst_sos_phase                        true
% 1.71/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.71/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.71/1.04  --inst_lit_sel_side                     none
% 1.71/1.04  --inst_solver_per_active                1400
% 1.71/1.04  --inst_solver_calls_frac                1.
% 1.71/1.04  --inst_passive_queue_type               priority_queues
% 1.71/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.71/1.04  --inst_passive_queues_freq              [25;2]
% 1.71/1.04  --inst_dismatching                      true
% 1.71/1.04  --inst_eager_unprocessed_to_passive     true
% 1.71/1.04  --inst_prop_sim_given                   true
% 1.71/1.04  --inst_prop_sim_new                     false
% 1.71/1.04  --inst_subs_new                         false
% 1.71/1.04  --inst_eq_res_simp                      false
% 1.71/1.04  --inst_subs_given                       false
% 1.71/1.04  --inst_orphan_elimination               true
% 1.71/1.04  --inst_learning_loop_flag               true
% 1.71/1.04  --inst_learning_start                   3000
% 1.71/1.04  --inst_learning_factor                  2
% 1.71/1.04  --inst_start_prop_sim_after_learn       3
% 1.71/1.04  --inst_sel_renew                        solver
% 1.71/1.04  --inst_lit_activity_flag                true
% 1.71/1.04  --inst_restr_to_given                   false
% 1.71/1.04  --inst_activity_threshold               500
% 1.71/1.04  --inst_out_proof                        true
% 1.71/1.04  
% 1.71/1.04  ------ Resolution Options
% 1.71/1.04  
% 1.71/1.04  --resolution_flag                       false
% 1.71/1.04  --res_lit_sel                           adaptive
% 1.71/1.04  --res_lit_sel_side                      none
% 1.71/1.04  --res_ordering                          kbo
% 1.71/1.04  --res_to_prop_solver                    active
% 1.71/1.04  --res_prop_simpl_new                    false
% 1.71/1.04  --res_prop_simpl_given                  true
% 1.71/1.04  --res_passive_queue_type                priority_queues
% 1.71/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.71/1.04  --res_passive_queues_freq               [15;5]
% 1.71/1.04  --res_forward_subs                      full
% 1.71/1.04  --res_backward_subs                     full
% 1.71/1.04  --res_forward_subs_resolution           true
% 1.71/1.04  --res_backward_subs_resolution          true
% 1.71/1.04  --res_orphan_elimination                true
% 1.71/1.04  --res_time_limit                        2.
% 1.71/1.04  --res_out_proof                         true
% 1.71/1.04  
% 1.71/1.04  ------ Superposition Options
% 1.71/1.04  
% 1.71/1.04  --superposition_flag                    true
% 1.71/1.04  --sup_passive_queue_type                priority_queues
% 1.71/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.71/1.04  --sup_passive_queues_freq               [8;1;4]
% 1.71/1.04  --demod_completeness_check              fast
% 1.71/1.04  --demod_use_ground                      true
% 1.71/1.04  --sup_to_prop_solver                    passive
% 1.71/1.04  --sup_prop_simpl_new                    true
% 1.71/1.04  --sup_prop_simpl_given                  true
% 1.71/1.04  --sup_fun_splitting                     false
% 1.71/1.04  --sup_smt_interval                      50000
% 1.71/1.04  
% 1.71/1.04  ------ Superposition Simplification Setup
% 1.71/1.04  
% 1.71/1.04  --sup_indices_passive                   []
% 1.71/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 1.71/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/1.04  --sup_full_bw                           [BwDemod]
% 1.71/1.04  --sup_immed_triv                        [TrivRules]
% 1.71/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.71/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/1.04  --sup_immed_bw_main                     []
% 1.71/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 1.71/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/1.04  
% 1.71/1.04  ------ Combination Options
% 1.71/1.04  
% 1.71/1.04  --comb_res_mult                         3
% 1.71/1.04  --comb_sup_mult                         2
% 1.71/1.04  --comb_inst_mult                        10
% 1.71/1.04  
% 1.71/1.04  ------ Debug Options
% 1.71/1.04  
% 1.71/1.04  --dbg_backtrace                         false
% 1.71/1.04  --dbg_dump_prop_clauses                 false
% 1.71/1.04  --dbg_dump_prop_clauses_file            -
% 1.71/1.04  --dbg_out_stat                          false
% 1.71/1.04  
% 1.71/1.04  
% 1.71/1.04  
% 1.71/1.04  
% 1.71/1.04  ------ Proving...
% 1.71/1.04  
% 1.71/1.04  
% 1.71/1.04  % SZS status Theorem for theBenchmark.p
% 1.71/1.04  
% 1.71/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 1.71/1.04  
% 1.71/1.04  fof(f1,axiom,(
% 1.71/1.04    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.04  
% 1.71/1.04  fof(f16,plain,(
% 1.71/1.04    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.71/1.04    inference(pure_predicate_removal,[],[f1])).
% 1.71/1.04  
% 1.71/1.04  fof(f17,plain,(
% 1.71/1.04    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.71/1.04    inference(ennf_transformation,[],[f16])).
% 1.71/1.04  
% 1.71/1.04  fof(f18,plain,(
% 1.71/1.04    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.71/1.04    inference(flattening,[],[f17])).
% 1.71/1.04  
% 1.71/1.04  fof(f66,plain,(
% 1.71/1.04    ( ! [X0] : (v7_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.71/1.04    inference(cnf_transformation,[],[f18])).
% 1.71/1.04  
% 1.71/1.04  fof(f13,axiom,(
% 1.71/1.04    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)))))))),
% 1.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.04  
% 1.71/1.04  fof(f40,plain,(
% 1.71/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) | ~r1_lattices(X0,X1,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v7_lattices(X0) | v2_struct_0(X0)))),
% 1.71/1.04    inference(ennf_transformation,[],[f13])).
% 1.71/1.04  
% 1.71/1.04  fof(f41,plain,(
% 1.71/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v7_lattices(X0) | v2_struct_0(X0))),
% 1.71/1.04    inference(flattening,[],[f40])).
% 1.71/1.04  
% 1.71/1.04  fof(f92,plain,(
% 1.71/1.04    ( ! [X2,X0,X3,X1] : (r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v7_lattices(X0) | v2_struct_0(X0)) )),
% 1.71/1.04    inference(cnf_transformation,[],[f41])).
% 1.71/1.04  
% 1.71/1.04  fof(f67,plain,(
% 1.71/1.04    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.71/1.04    inference(cnf_transformation,[],[f18])).
% 1.71/1.04  
% 1.71/1.04  fof(f68,plain,(
% 1.71/1.04    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.71/1.04    inference(cnf_transformation,[],[f18])).
% 1.71/1.04  
% 1.71/1.04  fof(f14,conjecture,(
% 1.71/1.04    ! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,k6_lattices(X0),X1) = X1))),
% 1.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.04  
% 1.71/1.04  fof(f15,negated_conjecture,(
% 1.71/1.04    ~! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,k6_lattices(X0),X1) = X1))),
% 1.71/1.04    inference(negated_conjecture,[],[f14])).
% 1.71/1.04  
% 1.71/1.04  fof(f42,plain,(
% 1.71/1.04    ? [X0] : (? [X1] : (k4_lattices(X0,k6_lattices(X0),X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.71/1.04    inference(ennf_transformation,[],[f15])).
% 1.71/1.04  
% 1.71/1.04  fof(f43,plain,(
% 1.71/1.04    ? [X0] : (? [X1] : (k4_lattices(X0,k6_lattices(X0),X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.71/1.04    inference(flattening,[],[f42])).
% 1.71/1.04  
% 1.71/1.04  fof(f61,plain,(
% 1.71/1.04    ( ! [X0] : (? [X1] : (k4_lattices(X0,k6_lattices(X0),X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) => (k4_lattices(X0,k6_lattices(X0),sK6) != sK6 & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 1.71/1.04    introduced(choice_axiom,[])).
% 1.71/1.04  
% 1.71/1.04  fof(f60,plain,(
% 1.71/1.04    ? [X0] : (? [X1] : (k4_lattices(X0,k6_lattices(X0),X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (k4_lattices(sK5,k6_lattices(sK5),X1) != X1 & m1_subset_1(X1,u1_struct_0(sK5))) & l3_lattices(sK5) & v14_lattices(sK5) & v10_lattices(sK5) & ~v2_struct_0(sK5))),
% 1.71/1.04    introduced(choice_axiom,[])).
% 1.71/1.04  
% 1.71/1.04  fof(f62,plain,(
% 1.71/1.04    (k4_lattices(sK5,k6_lattices(sK5),sK6) != sK6 & m1_subset_1(sK6,u1_struct_0(sK5))) & l3_lattices(sK5) & v14_lattices(sK5) & v10_lattices(sK5) & ~v2_struct_0(sK5)),
% 1.71/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f43,f61,f60])).
% 1.71/1.04  
% 1.71/1.04  fof(f94,plain,(
% 1.71/1.04    v10_lattices(sK5)),
% 1.71/1.04    inference(cnf_transformation,[],[f62])).
% 1.71/1.04  
% 1.71/1.04  fof(f93,plain,(
% 1.71/1.04    ~v2_struct_0(sK5)),
% 1.71/1.04    inference(cnf_transformation,[],[f62])).
% 1.71/1.04  
% 1.71/1.04  fof(f96,plain,(
% 1.71/1.04    l3_lattices(sK5)),
% 1.71/1.04    inference(cnf_transformation,[],[f62])).
% 1.71/1.04  
% 1.71/1.04  fof(f11,axiom,(
% 1.71/1.04    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 1.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.04  
% 1.71/1.04  fof(f36,plain,(
% 1.71/1.04    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 1.71/1.04    inference(ennf_transformation,[],[f11])).
% 1.71/1.04  
% 1.71/1.04  fof(f37,plain,(
% 1.71/1.04    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.71/1.04    inference(flattening,[],[f36])).
% 1.71/1.04  
% 1.71/1.04  fof(f59,plain,(
% 1.71/1.04    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.71/1.04    inference(nnf_transformation,[],[f37])).
% 1.71/1.04  
% 1.71/1.04  fof(f90,plain,(
% 1.71/1.04    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 1.71/1.04    inference(cnf_transformation,[],[f59])).
% 1.71/1.04  
% 1.71/1.04  fof(f7,axiom,(
% 1.71/1.04    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 1.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.04  
% 1.71/1.04  fof(f29,plain,(
% 1.71/1.04    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 1.71/1.04    inference(ennf_transformation,[],[f7])).
% 1.71/1.04  
% 1.71/1.04  fof(f84,plain,(
% 1.71/1.04    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 1.71/1.04    inference(cnf_transformation,[],[f29])).
% 1.71/1.04  
% 1.71/1.04  fof(f6,axiom,(
% 1.71/1.04    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)))),
% 1.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.04  
% 1.71/1.04  fof(f27,plain,(
% 1.71/1.04    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 1.71/1.04    inference(ennf_transformation,[],[f6])).
% 1.71/1.04  
% 1.71/1.04  fof(f28,plain,(
% 1.71/1.04    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.71/1.04    inference(flattening,[],[f27])).
% 1.71/1.04  
% 1.71/1.04  fof(f82,plain,(
% 1.71/1.04    ( ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 1.71/1.04    inference(cnf_transformation,[],[f28])).
% 1.71/1.04  
% 1.71/1.04  fof(f97,plain,(
% 1.71/1.04    m1_subset_1(sK6,u1_struct_0(sK5))),
% 1.71/1.04    inference(cnf_transformation,[],[f62])).
% 1.71/1.04  
% 1.71/1.04  fof(f4,axiom,(
% 1.71/1.04    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 1.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.04  
% 1.71/1.04  fof(f23,plain,(
% 1.71/1.04    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.71/1.04    inference(ennf_transformation,[],[f4])).
% 1.71/1.04  
% 1.71/1.04  fof(f24,plain,(
% 1.71/1.04    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.71/1.04    inference(flattening,[],[f23])).
% 1.71/1.04  
% 1.71/1.04  fof(f53,plain,(
% 1.71/1.04    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.71/1.04    inference(nnf_transformation,[],[f24])).
% 1.71/1.04  
% 1.71/1.04  fof(f54,plain,(
% 1.71/1.04    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.71/1.04    inference(rectify,[],[f53])).
% 1.71/1.04  
% 1.71/1.04  fof(f56,plain,(
% 1.71/1.04    ( ! [X1] : (! [X0] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,X1,k1_lattices(X0,X1,sK4(X0))) != X1 & m1_subset_1(sK4(X0),u1_struct_0(X0))))) )),
% 1.71/1.04    introduced(choice_axiom,[])).
% 1.71/1.04  
% 1.71/1.04  fof(f55,plain,(
% 1.71/1.04    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK3(X0),k1_lattices(X0,sK3(X0),X2)) != sK3(X0) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 1.71/1.04    introduced(choice_axiom,[])).
% 1.71/1.04  
% 1.71/1.04  fof(f57,plain,(
% 1.71/1.04    ! [X0] : (((v9_lattices(X0) | ((k2_lattices(X0,sK3(X0),k1_lattices(X0,sK3(X0),sK4(X0))) != sK3(X0) & m1_subset_1(sK4(X0),u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.71/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f54,f56,f55])).
% 1.71/1.04  
% 1.71/1.04  fof(f77,plain,(
% 1.71/1.04    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v9_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.71/1.04    inference(cnf_transformation,[],[f57])).
% 1.71/1.04  
% 1.71/1.04  fof(f2,axiom,(
% 1.71/1.04    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => (v14_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k6_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1))))))),
% 1.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.04  
% 1.71/1.04  fof(f19,plain,(
% 1.71/1.04    ! [X0] : ((! [X1] : ((k6_lattices(X0) = X1 <=> ! [X2] : ((k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0)) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 1.71/1.04    inference(ennf_transformation,[],[f2])).
% 1.71/1.04  
% 1.71/1.04  fof(f20,plain,(
% 1.71/1.04    ! [X0] : (! [X1] : ((k6_lattices(X0) = X1 <=> ! [X2] : ((k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.71/1.04    inference(flattening,[],[f19])).
% 1.71/1.04  
% 1.71/1.04  fof(f44,plain,(
% 1.71/1.04    ! [X0] : (! [X1] : (((k6_lattices(X0) = X1 | ? [X2] : ((k1_lattices(X0,X2,X1) != X1 | k1_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k6_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.71/1.04    inference(nnf_transformation,[],[f20])).
% 1.71/1.04  
% 1.71/1.04  fof(f45,plain,(
% 1.71/1.04    ! [X0] : (! [X1] : (((k6_lattices(X0) = X1 | ? [X2] : ((k1_lattices(X0,X2,X1) != X1 | k1_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k1_lattices(X0,X3,X1) = X1 & k1_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k6_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.71/1.04    inference(rectify,[],[f44])).
% 1.71/1.04  
% 1.71/1.04  fof(f46,plain,(
% 1.71/1.04    ! [X1,X0] : (? [X2] : ((k1_lattices(X0,X2,X1) != X1 | k1_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k1_lattices(X0,sK0(X0,X1),X1) != X1 | k1_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0))))),
% 1.71/1.04    introduced(choice_axiom,[])).
% 1.71/1.04  
% 1.71/1.04  fof(f47,plain,(
% 1.71/1.04    ! [X0] : (! [X1] : (((k6_lattices(X0) = X1 | ((k1_lattices(X0,sK0(X0,X1),X1) != X1 | k1_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k1_lattices(X0,X3,X1) = X1 & k1_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k6_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.71/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).
% 1.71/1.04  
% 1.71/1.04  fof(f70,plain,(
% 1.71/1.04    ( ! [X0,X3,X1] : (k1_lattices(X0,X3,X1) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k6_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 1.71/1.04    inference(cnf_transformation,[],[f47])).
% 1.71/1.04  
% 1.71/1.04  fof(f99,plain,(
% 1.71/1.04    ( ! [X0,X3] : (k6_lattices(X0) = k1_lattices(X0,X3,k6_lattices(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 1.71/1.04    inference(equality_resolution,[],[f70])).
% 1.71/1.04  
% 1.71/1.04  fof(f95,plain,(
% 1.71/1.04    v14_lattices(sK5)),
% 1.71/1.04    inference(cnf_transformation,[],[f62])).
% 1.71/1.04  
% 1.71/1.04  fof(f3,axiom,(
% 1.71/1.04    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 1.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.04  
% 1.71/1.04  fof(f21,plain,(
% 1.71/1.04    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.71/1.04    inference(ennf_transformation,[],[f3])).
% 1.71/1.04  
% 1.71/1.04  fof(f22,plain,(
% 1.71/1.04    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.71/1.04    inference(flattening,[],[f21])).
% 1.71/1.04  
% 1.71/1.04  fof(f48,plain,(
% 1.71/1.04    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.71/1.04    inference(nnf_transformation,[],[f22])).
% 1.71/1.04  
% 1.71/1.04  fof(f49,plain,(
% 1.71/1.04    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.71/1.04    inference(rectify,[],[f48])).
% 1.71/1.04  
% 1.71/1.04  fof(f51,plain,(
% 1.71/1.04    ( ! [X1] : (! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (k1_lattices(X0,k2_lattices(X0,X1,sK2(X0)),sK2(X0)) != sK2(X0) & m1_subset_1(sK2(X0),u1_struct_0(X0))))) )),
% 1.71/1.04    introduced(choice_axiom,[])).
% 1.71/1.04  
% 1.71/1.04  fof(f50,plain,(
% 1.71/1.04    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK1(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK1(X0),u1_struct_0(X0))))),
% 1.71/1.04    introduced(choice_axiom,[])).
% 1.71/1.04  
% 1.71/1.04  fof(f52,plain,(
% 1.71/1.04    ! [X0] : (((v8_lattices(X0) | ((k1_lattices(X0,k2_lattices(X0,sK1(X0),sK2(X0)),sK2(X0)) != sK2(X0) & m1_subset_1(sK2(X0),u1_struct_0(X0))) & m1_subset_1(sK1(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.71/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f49,f51,f50])).
% 1.71/1.04  
% 1.71/1.04  fof(f73,plain,(
% 1.71/1.04    ( ! [X4,X0,X3] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v8_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.71/1.04    inference(cnf_transformation,[],[f52])).
% 1.71/1.04  
% 1.71/1.04  fof(f83,plain,(
% 1.71/1.04    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 1.71/1.04    inference(cnf_transformation,[],[f29])).
% 1.71/1.04  
% 1.71/1.04  fof(f5,axiom,(
% 1.71/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 1.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.04  
% 1.71/1.04  fof(f25,plain,(
% 1.71/1.04    ! [X0,X1,X2] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.71/1.04    inference(ennf_transformation,[],[f5])).
% 1.71/1.04  
% 1.71/1.04  fof(f26,plain,(
% 1.71/1.04    ! [X0,X1,X2] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.71/1.04    inference(flattening,[],[f25])).
% 1.71/1.04  
% 1.71/1.04  fof(f81,plain,(
% 1.71/1.04    ( ! [X2,X0,X1] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 1.71/1.04    inference(cnf_transformation,[],[f26])).
% 1.71/1.04  
% 1.71/1.04  fof(f64,plain,(
% 1.71/1.04    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.71/1.04    inference(cnf_transformation,[],[f18])).
% 1.71/1.04  
% 1.71/1.04  fof(f12,axiom,(
% 1.71/1.04    ! [X0] : ((l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_lattices(X0,X2,X1) & r1_lattices(X0,X1,X2)) => X1 = X2))))),
% 1.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.04  
% 1.71/1.04  fof(f38,plain,(
% 1.71/1.04    ! [X0] : (! [X1] : (! [X2] : ((X1 = X2 | (~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 1.71/1.04    inference(ennf_transformation,[],[f12])).
% 1.71/1.04  
% 1.71/1.04  fof(f39,plain,(
% 1.71/1.04    ! [X0] : (! [X1] : (! [X2] : (X1 = X2 | ~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 1.71/1.04    inference(flattening,[],[f38])).
% 1.71/1.04  
% 1.71/1.04  fof(f91,plain,(
% 1.71/1.04    ( ! [X2,X0,X1] : (X1 = X2 | ~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 1.71/1.04    inference(cnf_transformation,[],[f39])).
% 1.71/1.04  
% 1.71/1.04  fof(f8,axiom,(
% 1.71/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2))),
% 1.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.04  
% 1.71/1.04  fof(f30,plain,(
% 1.71/1.04    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.71/1.04    inference(ennf_transformation,[],[f8])).
% 1.71/1.04  
% 1.71/1.04  fof(f31,plain,(
% 1.71/1.04    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.71/1.04    inference(flattening,[],[f30])).
% 1.71/1.04  
% 1.71/1.04  fof(f85,plain,(
% 1.71/1.04    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.71/1.04    inference(cnf_transformation,[],[f31])).
% 1.71/1.04  
% 1.71/1.04  fof(f65,plain,(
% 1.71/1.04    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.71/1.04    inference(cnf_transformation,[],[f18])).
% 1.71/1.04  
% 1.71/1.04  fof(f89,plain,(
% 1.71/1.04    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 1.71/1.04    inference(cnf_transformation,[],[f59])).
% 1.71/1.04  
% 1.71/1.04  fof(f10,axiom,(
% 1.71/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => r3_lattices(X0,X1,X1))),
% 1.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.04  
% 1.71/1.04  fof(f34,plain,(
% 1.71/1.04    ! [X0,X1,X2] : (r3_lattices(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.71/1.04    inference(ennf_transformation,[],[f10])).
% 1.71/1.04  
% 1.71/1.04  fof(f35,plain,(
% 1.71/1.04    ! [X0,X1,X2] : (r3_lattices(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.71/1.04    inference(flattening,[],[f34])).
% 1.71/1.04  
% 1.71/1.04  fof(f88,plain,(
% 1.71/1.04    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.71/1.04    inference(cnf_transformation,[],[f35])).
% 1.71/1.04  
% 1.71/1.04  fof(f9,axiom,(
% 1.71/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 1.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.71/1.04  
% 1.71/1.04  fof(f32,plain,(
% 1.71/1.04    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.71/1.04    inference(ennf_transformation,[],[f9])).
% 1.71/1.04  
% 1.71/1.04  fof(f33,plain,(
% 1.71/1.04    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.71/1.04    inference(flattening,[],[f32])).
% 1.71/1.04  
% 1.71/1.04  fof(f58,plain,(
% 1.71/1.04    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.71/1.04    inference(nnf_transformation,[],[f33])).
% 1.71/1.04  
% 1.71/1.04  fof(f86,plain,(
% 1.71/1.04    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.71/1.04    inference(cnf_transformation,[],[f58])).
% 1.71/1.04  
% 1.71/1.04  fof(f98,plain,(
% 1.71/1.04    k4_lattices(sK5,k6_lattices(sK5),sK6) != sK6),
% 1.71/1.04    inference(cnf_transformation,[],[f62])).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1154,plain,
% 1.71/1.04      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 1.71/1.04      theory(equality) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_4214,plain,
% 1.71/1.04      ( X0_54 != X1_54
% 1.71/1.04      | X0_54 = k1_lattices(sK5,X2_54,X3_54)
% 1.71/1.04      | k1_lattices(sK5,X2_54,X3_54) != X1_54 ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_1154]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_12832,plain,
% 1.71/1.04      ( k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),sK6) != X0_54
% 1.71/1.04      | sK6 != X0_54
% 1.71/1.04      | sK6 = k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),sK6) ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_4214]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_12833,plain,
% 1.71/1.04      ( k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),sK6) != sK6
% 1.71/1.04      | sK6 = k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),sK6)
% 1.71/1.04      | sK6 != sK6 ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_12832]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1159,plain,
% 1.71/1.04      ( ~ r1_lattices(X0_56,X0_54,X1_54)
% 1.71/1.04      | r1_lattices(X0_56,X2_54,X3_54)
% 1.71/1.04      | X2_54 != X0_54
% 1.71/1.04      | X3_54 != X1_54 ),
% 1.71/1.04      theory(equality) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_3329,plain,
% 1.71/1.04      ( ~ r1_lattices(sK5,X0_54,X1_54)
% 1.71/1.04      | r1_lattices(sK5,X2_54,k4_lattices(sK5,k6_lattices(sK5),sK6))
% 1.71/1.04      | X2_54 != X0_54
% 1.71/1.04      | k4_lattices(sK5,k6_lattices(sK5),sK6) != X1_54 ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_1159]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_6952,plain,
% 1.71/1.04      ( r1_lattices(sK5,X0_54,k4_lattices(sK5,k6_lattices(sK5),sK6))
% 1.71/1.04      | ~ r1_lattices(sK5,X1_54,k2_lattices(sK5,k6_lattices(sK5),sK6))
% 1.71/1.04      | X0_54 != X1_54
% 1.71/1.04      | k4_lattices(sK5,k6_lattices(sK5),sK6) != k2_lattices(sK5,k6_lattices(sK5),sK6) ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_3329]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_9859,plain,
% 1.71/1.04      ( r1_lattices(sK5,X0_54,k4_lattices(sK5,k6_lattices(sK5),sK6))
% 1.71/1.04      | ~ r1_lattices(sK5,k2_lattices(sK5,X1_54,sK6),k2_lattices(sK5,k6_lattices(sK5),sK6))
% 1.71/1.04      | X0_54 != k2_lattices(sK5,X1_54,sK6)
% 1.71/1.04      | k4_lattices(sK5,k6_lattices(sK5),sK6) != k2_lattices(sK5,k6_lattices(sK5),sK6) ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_6952]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_9861,plain,
% 1.71/1.04      ( ~ r1_lattices(sK5,k2_lattices(sK5,sK6,sK6),k2_lattices(sK5,k6_lattices(sK5),sK6))
% 1.71/1.04      | r1_lattices(sK5,sK6,k4_lattices(sK5,k6_lattices(sK5),sK6))
% 1.71/1.04      | k4_lattices(sK5,k6_lattices(sK5),sK6) != k2_lattices(sK5,k6_lattices(sK5),sK6)
% 1.71/1.04      | sK6 != k2_lattices(sK5,sK6,sK6) ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_9859]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1644,plain,
% 1.71/1.04      ( ~ r1_lattices(sK5,X0_54,X1_54)
% 1.71/1.04      | r1_lattices(sK5,k4_lattices(sK5,k6_lattices(sK5),sK6),sK6)
% 1.71/1.04      | k4_lattices(sK5,k6_lattices(sK5),sK6) != X0_54
% 1.71/1.04      | sK6 != X1_54 ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_1159]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1702,plain,
% 1.71/1.04      ( r1_lattices(sK5,k4_lattices(sK5,k6_lattices(sK5),sK6),sK6)
% 1.71/1.04      | ~ r1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),X0_54)
% 1.71/1.04      | k4_lattices(sK5,k6_lattices(sK5),sK6) != k2_lattices(sK5,k6_lattices(sK5),sK6)
% 1.71/1.04      | sK6 != X0_54 ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_1644]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_5793,plain,
% 1.71/1.04      ( r1_lattices(sK5,k4_lattices(sK5,k6_lattices(sK5),sK6),sK6)
% 1.71/1.04      | ~ r1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),sK6))
% 1.71/1.04      | k4_lattices(sK5,k6_lattices(sK5),sK6) != k2_lattices(sK5,k6_lattices(sK5),sK6)
% 1.71/1.04      | sK6 != k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),sK6) ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_1702]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1156,plain,
% 1.71/1.04      ( ~ m1_subset_1(X0_54,X0_55)
% 1.71/1.04      | m1_subset_1(X1_54,X0_55)
% 1.71/1.04      | X1_54 != X0_54 ),
% 1.71/1.04      theory(equality) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1621,plain,
% 1.71/1.04      ( m1_subset_1(X0_54,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 1.71/1.04      | X0_54 != sK6 ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_1156]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_2341,plain,
% 1.71/1.04      ( m1_subset_1(k1_lattices(sK5,X0_54,X1_54),u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 1.71/1.04      | k1_lattices(sK5,X0_54,X1_54) != sK6 ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_1621]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_3042,plain,
% 1.71/1.04      ( m1_subset_1(k1_lattices(sK5,k2_lattices(sK5,X0_54,sK6),sK6),u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 1.71/1.04      | k1_lattices(sK5,k2_lattices(sK5,X0_54,sK6),sK6) != sK6 ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_2341]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_4434,plain,
% 1.71/1.04      ( m1_subset_1(k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),sK6),u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 1.71/1.04      | k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),sK6) != sK6 ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_3042]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_2,plain,
% 1.71/1.04      ( v7_lattices(X0)
% 1.71/1.04      | ~ l3_lattices(X0)
% 1.71/1.04      | v2_struct_0(X0)
% 1.71/1.04      | ~ v10_lattices(X0) ),
% 1.71/1.04      inference(cnf_transformation,[],[f66]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_29,plain,
% 1.71/1.04      ( ~ r1_lattices(X0,X1,X2)
% 1.71/1.04      | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
% 1.71/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.71/1.04      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.71/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.71/1.04      | ~ v7_lattices(X0)
% 1.71/1.04      | ~ v8_lattices(X0)
% 1.71/1.04      | ~ l3_lattices(X0)
% 1.71/1.04      | v2_struct_0(X0)
% 1.71/1.04      | ~ v9_lattices(X0) ),
% 1.71/1.04      inference(cnf_transformation,[],[f92]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_487,plain,
% 1.71/1.04      ( ~ r1_lattices(X0,X1,X2)
% 1.71/1.04      | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
% 1.71/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.71/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.71/1.04      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.71/1.04      | ~ v8_lattices(X0)
% 1.71/1.04      | ~ l3_lattices(X0)
% 1.71/1.04      | v2_struct_0(X0)
% 1.71/1.04      | ~ v10_lattices(X0)
% 1.71/1.04      | ~ v9_lattices(X0) ),
% 1.71/1.04      inference(resolution,[status(thm)],[c_2,c_29]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1,plain,
% 1.71/1.04      ( v8_lattices(X0)
% 1.71/1.04      | ~ l3_lattices(X0)
% 1.71/1.04      | v2_struct_0(X0)
% 1.71/1.04      | ~ v10_lattices(X0) ),
% 1.71/1.04      inference(cnf_transformation,[],[f67]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_0,plain,
% 1.71/1.04      ( ~ l3_lattices(X0)
% 1.71/1.04      | v2_struct_0(X0)
% 1.71/1.04      | ~ v10_lattices(X0)
% 1.71/1.04      | v9_lattices(X0) ),
% 1.71/1.04      inference(cnf_transformation,[],[f68]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_491,plain,
% 1.71/1.04      ( ~ v10_lattices(X0)
% 1.71/1.04      | v2_struct_0(X0)
% 1.71/1.04      | ~ l3_lattices(X0)
% 1.71/1.04      | ~ r1_lattices(X0,X1,X2)
% 1.71/1.04      | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
% 1.71/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.71/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.71/1.04      | ~ m1_subset_1(X3,u1_struct_0(X0)) ),
% 1.71/1.04      inference(global_propositional_subsumption,
% 1.71/1.04                [status(thm)],
% 1.71/1.04                [c_487,c_29,c_2,c_1,c_0]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_492,plain,
% 1.71/1.04      ( ~ r1_lattices(X0,X1,X2)
% 1.71/1.04      | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
% 1.71/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.71/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.71/1.04      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.71/1.04      | ~ l3_lattices(X0)
% 1.71/1.04      | v2_struct_0(X0)
% 1.71/1.04      | ~ v10_lattices(X0) ),
% 1.71/1.04      inference(renaming,[status(thm)],[c_491]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_34,negated_conjecture,
% 1.71/1.04      ( v10_lattices(sK5) ),
% 1.71/1.04      inference(cnf_transformation,[],[f94]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_645,plain,
% 1.71/1.04      ( ~ r1_lattices(X0,X1,X2)
% 1.71/1.04      | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
% 1.71/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.71/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.71/1.04      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.71/1.04      | ~ l3_lattices(X0)
% 1.71/1.04      | v2_struct_0(X0)
% 1.71/1.04      | sK5 != X0 ),
% 1.71/1.04      inference(resolution_lifted,[status(thm)],[c_492,c_34]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_646,plain,
% 1.71/1.04      ( ~ r1_lattices(sK5,X0,X1)
% 1.71/1.04      | r1_lattices(sK5,k2_lattices(sK5,X0,X2),k2_lattices(sK5,X1,X2))
% 1.71/1.04      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.71/1.04      | ~ l3_lattices(sK5)
% 1.71/1.04      | v2_struct_0(sK5) ),
% 1.71/1.04      inference(unflattening,[status(thm)],[c_645]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_35,negated_conjecture,
% 1.71/1.04      ( ~ v2_struct_0(sK5) ),
% 1.71/1.04      inference(cnf_transformation,[],[f93]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_32,negated_conjecture,
% 1.71/1.04      ( l3_lattices(sK5) ),
% 1.71/1.04      inference(cnf_transformation,[],[f96]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_650,plain,
% 1.71/1.04      ( ~ r1_lattices(sK5,X0,X1)
% 1.71/1.04      | r1_lattices(sK5,k2_lattices(sK5,X0,X2),k2_lattices(sK5,X1,X2))
% 1.71/1.04      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 1.71/1.04      inference(global_propositional_subsumption,
% 1.71/1.04                [status(thm)],
% 1.71/1.04                [c_646,c_35,c_32]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_651,plain,
% 1.71/1.04      ( ~ r1_lattices(sK5,X0,X1)
% 1.71/1.04      | r1_lattices(sK5,k2_lattices(sK5,X0,X2),k2_lattices(sK5,X1,X2))
% 1.71/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
% 1.71/1.04      inference(renaming,[status(thm)],[c_650]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1142,plain,
% 1.71/1.04      ( ~ r1_lattices(sK5,X0_54,X1_54)
% 1.71/1.04      | r1_lattices(sK5,k2_lattices(sK5,X0_54,X2_54),k2_lattices(sK5,X1_54,X2_54))
% 1.71/1.04      | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(X1_54,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(X2_54,u1_struct_0(sK5)) ),
% 1.71/1.04      inference(subtyping,[status(esa)],[c_651]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_2898,plain,
% 1.71/1.04      ( ~ r1_lattices(sK5,X0_54,k6_lattices(sK5))
% 1.71/1.04      | r1_lattices(sK5,k2_lattices(sK5,X0_54,sK6),k2_lattices(sK5,k6_lattices(sK5),sK6))
% 1.71/1.04      | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_1142]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_2904,plain,
% 1.71/1.04      ( r1_lattices(sK5,k2_lattices(sK5,sK6,sK6),k2_lattices(sK5,k6_lattices(sK5),sK6))
% 1.71/1.04      | ~ r1_lattices(sK5,sK6,k6_lattices(sK5))
% 1.71/1.04      | ~ m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_2898]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_26,plain,
% 1.71/1.04      ( r1_lattices(X0,X1,X2)
% 1.71/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.71/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.71/1.04      | ~ v8_lattices(X0)
% 1.71/1.04      | ~ l3_lattices(X0)
% 1.71/1.04      | v2_struct_0(X0)
% 1.71/1.04      | ~ v9_lattices(X0)
% 1.71/1.04      | k2_lattices(X0,X1,X2) != X1 ),
% 1.71/1.04      inference(cnf_transformation,[],[f90]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_911,plain,
% 1.71/1.04      ( r1_lattices(X0,X1,X2)
% 1.71/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.71/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.71/1.04      | ~ v8_lattices(X0)
% 1.71/1.04      | ~ l3_lattices(X0)
% 1.71/1.04      | ~ v9_lattices(X0)
% 1.71/1.04      | k2_lattices(X0,X1,X2) != X1
% 1.71/1.04      | sK5 != X0 ),
% 1.71/1.04      inference(resolution_lifted,[status(thm)],[c_26,c_35]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_912,plain,
% 1.71/1.04      ( r1_lattices(sK5,X0,X1)
% 1.71/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.71/1.04      | ~ v8_lattices(sK5)
% 1.71/1.04      | ~ l3_lattices(sK5)
% 1.71/1.04      | ~ v9_lattices(sK5)
% 1.71/1.04      | k2_lattices(sK5,X0,X1) != X0 ),
% 1.71/1.04      inference(unflattening,[status(thm)],[c_911]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_124,plain,
% 1.71/1.04      ( v8_lattices(sK5)
% 1.71/1.04      | ~ l3_lattices(sK5)
% 1.71/1.04      | v2_struct_0(sK5)
% 1.71/1.04      | ~ v10_lattices(sK5) ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_1]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_127,plain,
% 1.71/1.04      ( ~ l3_lattices(sK5)
% 1.71/1.04      | v2_struct_0(sK5)
% 1.71/1.04      | ~ v10_lattices(sK5)
% 1.71/1.04      | v9_lattices(sK5) ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_0]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_914,plain,
% 1.71/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.71/1.04      | r1_lattices(sK5,X0,X1)
% 1.71/1.04      | k2_lattices(sK5,X0,X1) != X0 ),
% 1.71/1.04      inference(global_propositional_subsumption,
% 1.71/1.04                [status(thm)],
% 1.71/1.04                [c_912,c_35,c_34,c_32,c_124,c_127]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_915,plain,
% 1.71/1.04      ( r1_lattices(sK5,X0,X1)
% 1.71/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.71/1.04      | k2_lattices(sK5,X0,X1) != X0 ),
% 1.71/1.04      inference(renaming,[status(thm)],[c_914]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1136,plain,
% 1.71/1.04      ( r1_lattices(sK5,X0_54,X1_54)
% 1.71/1.04      | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(X1_54,u1_struct_0(sK5))
% 1.71/1.04      | k2_lattices(sK5,X0_54,X1_54) != X0_54 ),
% 1.71/1.04      inference(subtyping,[status(esa)],[c_915]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1823,plain,
% 1.71/1.04      ( r1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),X0_54)
% 1.71/1.04      | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(k2_lattices(sK5,k6_lattices(sK5),sK6),u1_struct_0(sK5))
% 1.71/1.04      | k2_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),X0_54) != k2_lattices(sK5,k6_lattices(sK5),sK6) ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_1136]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_2863,plain,
% 1.71/1.04      ( r1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),X0_54))
% 1.71/1.04      | ~ m1_subset_1(k2_lattices(sK5,k6_lattices(sK5),sK6),u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),X0_54),u1_struct_0(sK5))
% 1.71/1.04      | k2_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),X0_54)) != k2_lattices(sK5,k6_lattices(sK5),sK6) ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_1823]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_2865,plain,
% 1.71/1.04      ( r1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),sK6))
% 1.71/1.04      | ~ m1_subset_1(k2_lattices(sK5,k6_lattices(sK5),sK6),u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),sK6),u1_struct_0(sK5))
% 1.71/1.04      | k2_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),sK6)) != k2_lattices(sK5,k6_lattices(sK5),sK6) ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_2863]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_20,plain,
% 1.71/1.04      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 1.71/1.04      inference(cnf_transformation,[],[f84]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_19,plain,
% 1.71/1.04      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
% 1.71/1.04      | ~ l2_lattices(X0)
% 1.71/1.04      | v2_struct_0(X0) ),
% 1.71/1.04      inference(cnf_transformation,[],[f82]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_627,plain,
% 1.71/1.04      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
% 1.71/1.04      | ~ l3_lattices(X0)
% 1.71/1.04      | v2_struct_0(X0) ),
% 1.71/1.04      inference(resolution,[status(thm)],[c_20,c_19]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_876,plain,
% 1.71/1.04      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
% 1.71/1.04      | ~ l3_lattices(X0)
% 1.71/1.04      | sK5 != X0 ),
% 1.71/1.04      inference(resolution_lifted,[status(thm)],[c_627,c_35]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_877,plain,
% 1.71/1.04      ( m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5))
% 1.71/1.04      | ~ l3_lattices(sK5) ),
% 1.71/1.04      inference(unflattening,[status(thm)],[c_876]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_69,plain,
% 1.71/1.04      ( l2_lattices(sK5) | ~ l3_lattices(sK5) ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_20]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_72,plain,
% 1.71/1.04      ( m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5))
% 1.71/1.04      | ~ l2_lattices(sK5)
% 1.71/1.04      | v2_struct_0(sK5) ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_19]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_879,plain,
% 1.71/1.04      ( m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5)) ),
% 1.71/1.04      inference(global_propositional_subsumption,
% 1.71/1.04                [status(thm)],
% 1.71/1.04                [c_877,c_35,c_32,c_69,c_72]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1138,plain,
% 1.71/1.04      ( m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5)) ),
% 1.71/1.04      inference(subtyping,[status(esa)],[c_879]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1472,plain,
% 1.71/1.04      ( m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5)) = iProver_top ),
% 1.71/1.04      inference(predicate_to_equality,[status(thm)],[c_1138]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_31,negated_conjecture,
% 1.71/1.04      ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 1.71/1.04      inference(cnf_transformation,[],[f97]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1147,negated_conjecture,
% 1.71/1.04      ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 1.71/1.04      inference(subtyping,[status(esa)],[c_31]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1461,plain,
% 1.71/1.04      ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
% 1.71/1.04      inference(predicate_to_equality,[status(thm)],[c_1147]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_17,plain,
% 1.71/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.71/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.71/1.04      | ~ l3_lattices(X1)
% 1.71/1.04      | v2_struct_0(X1)
% 1.71/1.04      | ~ v9_lattices(X1)
% 1.71/1.04      | k2_lattices(X1,X0,k1_lattices(X1,X0,X2)) = X0 ),
% 1.71/1.04      inference(cnf_transformation,[],[f77]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_964,plain,
% 1.71/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.71/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.71/1.04      | ~ l3_lattices(X1)
% 1.71/1.04      | ~ v9_lattices(X1)
% 1.71/1.04      | k2_lattices(X1,X0,k1_lattices(X1,X0,X2)) = X0
% 1.71/1.04      | sK5 != X1 ),
% 1.71/1.04      inference(resolution_lifted,[status(thm)],[c_17,c_35]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_965,plain,
% 1.71/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.71/1.04      | ~ l3_lattices(sK5)
% 1.71/1.04      | ~ v9_lattices(sK5)
% 1.71/1.04      | k2_lattices(sK5,X0,k1_lattices(sK5,X0,X1)) = X0 ),
% 1.71/1.04      inference(unflattening,[status(thm)],[c_964]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_969,plain,
% 1.71/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.71/1.04      | k2_lattices(sK5,X0,k1_lattices(sK5,X0,X1)) = X0 ),
% 1.71/1.04      inference(global_propositional_subsumption,
% 1.71/1.04                [status(thm)],
% 1.71/1.04                [c_965,c_35,c_34,c_32,c_127]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1134,plain,
% 1.71/1.04      ( ~ m1_subset_1(X0_54,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(X1_54,u1_struct_0(sK5))
% 1.71/1.04      | k2_lattices(sK5,X0_54,k1_lattices(sK5,X0_54,X1_54)) = X0_54 ),
% 1.71/1.04      inference(subtyping,[status(esa)],[c_969]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1476,plain,
% 1.71/1.04      ( k2_lattices(sK5,X0_54,k1_lattices(sK5,X0_54,X1_54)) = X0_54
% 1.71/1.04      | m1_subset_1(X0_54,u1_struct_0(sK5)) != iProver_top
% 1.71/1.04      | m1_subset_1(X1_54,u1_struct_0(sK5)) != iProver_top ),
% 1.71/1.04      inference(predicate_to_equality,[status(thm)],[c_1134]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1885,plain,
% 1.71/1.04      ( k2_lattices(sK5,sK6,k1_lattices(sK5,sK6,X0_54)) = sK6
% 1.71/1.04      | m1_subset_1(X0_54,u1_struct_0(sK5)) != iProver_top ),
% 1.71/1.04      inference(superposition,[status(thm)],[c_1461,c_1476]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_2073,plain,
% 1.71/1.04      ( k2_lattices(sK5,sK6,k1_lattices(sK5,sK6,k6_lattices(sK5))) = sK6 ),
% 1.71/1.04      inference(superposition,[status(thm)],[c_1472,c_1885]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_8,plain,
% 1.71/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.71/1.04      | ~ m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
% 1.71/1.04      | ~ l2_lattices(X1)
% 1.71/1.04      | ~ v14_lattices(X1)
% 1.71/1.04      | v2_struct_0(X1)
% 1.71/1.04      | k1_lattices(X1,X0,k6_lattices(X1)) = k6_lattices(X1) ),
% 1.71/1.04      inference(cnf_transformation,[],[f99]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_33,negated_conjecture,
% 1.71/1.04      ( v14_lattices(sK5) ),
% 1.71/1.04      inference(cnf_transformation,[],[f95]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_549,plain,
% 1.71/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.71/1.04      | ~ m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
% 1.71/1.04      | ~ l2_lattices(X1)
% 1.71/1.04      | v2_struct_0(X1)
% 1.71/1.04      | k1_lattices(X1,X0,k6_lattices(X1)) = k6_lattices(X1)
% 1.71/1.04      | sK5 != X1 ),
% 1.71/1.04      inference(resolution_lifted,[status(thm)],[c_8,c_33]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_550,plain,
% 1.71/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5))
% 1.71/1.04      | ~ l2_lattices(sK5)
% 1.71/1.04      | v2_struct_0(sK5)
% 1.71/1.04      | k1_lattices(sK5,X0,k6_lattices(sK5)) = k6_lattices(sK5) ),
% 1.71/1.04      inference(unflattening,[status(thm)],[c_549]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_554,plain,
% 1.71/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.71/1.04      | k1_lattices(sK5,X0,k6_lattices(sK5)) = k6_lattices(sK5) ),
% 1.71/1.04      inference(global_propositional_subsumption,
% 1.71/1.04                [status(thm)],
% 1.71/1.04                [c_550,c_35,c_32,c_69,c_72]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1145,plain,
% 1.71/1.04      ( ~ m1_subset_1(X0_54,u1_struct_0(sK5))
% 1.71/1.04      | k1_lattices(sK5,X0_54,k6_lattices(sK5)) = k6_lattices(sK5) ),
% 1.71/1.04      inference(subtyping,[status(esa)],[c_554]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1463,plain,
% 1.71/1.04      ( k1_lattices(sK5,X0_54,k6_lattices(sK5)) = k6_lattices(sK5)
% 1.71/1.04      | m1_subset_1(X0_54,u1_struct_0(sK5)) != iProver_top ),
% 1.71/1.04      inference(predicate_to_equality,[status(thm)],[c_1145]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1670,plain,
% 1.71/1.04      ( k1_lattices(sK5,sK6,k6_lattices(sK5)) = k6_lattices(sK5) ),
% 1.71/1.04      inference(superposition,[status(thm)],[c_1461,c_1463]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_2089,plain,
% 1.71/1.04      ( k2_lattices(sK5,sK6,k6_lattices(sK5)) = sK6 ),
% 1.71/1.04      inference(light_normalisation,[status(thm)],[c_2073,c_1670]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1474,plain,
% 1.71/1.04      ( k2_lattices(sK5,X0_54,X1_54) != X0_54
% 1.71/1.04      | r1_lattices(sK5,X0_54,X1_54) = iProver_top
% 1.71/1.04      | m1_subset_1(X0_54,u1_struct_0(sK5)) != iProver_top
% 1.71/1.04      | m1_subset_1(X1_54,u1_struct_0(sK5)) != iProver_top ),
% 1.71/1.04      inference(predicate_to_equality,[status(thm)],[c_1136]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_2405,plain,
% 1.71/1.04      ( r1_lattices(sK5,sK6,k6_lattices(sK5)) = iProver_top
% 1.71/1.04      | m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5)) != iProver_top
% 1.71/1.04      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
% 1.71/1.04      inference(superposition,[status(thm)],[c_2089,c_1474]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_2419,plain,
% 1.71/1.04      ( r1_lattices(sK5,sK6,k6_lattices(sK5))
% 1.71/1.04      | ~ m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 1.71/1.04      inference(predicate_to_equality_rev,[status(thm)],[c_2405]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_13,plain,
% 1.71/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.71/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.71/1.04      | ~ v8_lattices(X1)
% 1.71/1.04      | ~ l3_lattices(X1)
% 1.71/1.04      | v2_struct_0(X1)
% 1.71/1.04      | k1_lattices(X1,k2_lattices(X1,X0,X2),X2) = X2 ),
% 1.71/1.04      inference(cnf_transformation,[],[f73]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_985,plain,
% 1.71/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.71/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.71/1.04      | ~ v8_lattices(X1)
% 1.71/1.04      | ~ l3_lattices(X1)
% 1.71/1.04      | k1_lattices(X1,k2_lattices(X1,X0,X2),X2) = X2
% 1.71/1.04      | sK5 != X1 ),
% 1.71/1.04      inference(resolution_lifted,[status(thm)],[c_13,c_35]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_986,plain,
% 1.71/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.71/1.04      | ~ v8_lattices(sK5)
% 1.71/1.04      | ~ l3_lattices(sK5)
% 1.71/1.04      | k1_lattices(sK5,k2_lattices(sK5,X0,X1),X1) = X1 ),
% 1.71/1.04      inference(unflattening,[status(thm)],[c_985]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_990,plain,
% 1.71/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.71/1.04      | k1_lattices(sK5,k2_lattices(sK5,X0,X1),X1) = X1 ),
% 1.71/1.04      inference(global_propositional_subsumption,
% 1.71/1.04                [status(thm)],
% 1.71/1.04                [c_986,c_35,c_34,c_32,c_124]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1133,plain,
% 1.71/1.04      ( ~ m1_subset_1(X0_54,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(X1_54,u1_struct_0(sK5))
% 1.71/1.04      | k1_lattices(sK5,k2_lattices(sK5,X0_54,X1_54),X1_54) = X1_54 ),
% 1.71/1.04      inference(subtyping,[status(esa)],[c_990]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1477,plain,
% 1.71/1.04      ( k1_lattices(sK5,k2_lattices(sK5,X0_54,X1_54),X1_54) = X1_54
% 1.71/1.04      | m1_subset_1(X0_54,u1_struct_0(sK5)) != iProver_top
% 1.71/1.04      | m1_subset_1(X1_54,u1_struct_0(sK5)) != iProver_top ),
% 1.71/1.04      inference(predicate_to_equality,[status(thm)],[c_1133]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_2150,plain,
% 1.71/1.04      ( k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),X0_54),X0_54) = X0_54
% 1.71/1.04      | m1_subset_1(X0_54,u1_struct_0(sK5)) != iProver_top ),
% 1.71/1.04      inference(superposition,[status(thm)],[c_1472,c_1477]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_2179,plain,
% 1.71/1.04      ( k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),sK6) = sK6
% 1.71/1.04      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_2150]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_2064,plain,
% 1.71/1.04      ( k2_lattices(sK5,X0_54,sK6) != X1_54
% 1.71/1.04      | sK6 != X1_54
% 1.71/1.04      | sK6 = k2_lattices(sK5,X0_54,sK6) ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_1154]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_2065,plain,
% 1.71/1.04      ( k2_lattices(sK5,sK6,sK6) != sK6
% 1.71/1.04      | sK6 = k2_lattices(sK5,sK6,sK6)
% 1.71/1.04      | sK6 != sK6 ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_2064]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_21,plain,
% 1.71/1.04      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 1.71/1.04      inference(cnf_transformation,[],[f83]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_18,plain,
% 1.71/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.71/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.71/1.04      | m1_subset_1(k2_lattices(X1,X0,X2),u1_struct_0(X1))
% 1.71/1.04      | ~ l1_lattices(X1)
% 1.71/1.04      | v2_struct_0(X1) ),
% 1.71/1.04      inference(cnf_transformation,[],[f81]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_453,plain,
% 1.71/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.71/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.71/1.04      | m1_subset_1(k2_lattices(X1,X0,X2),u1_struct_0(X1))
% 1.71/1.04      | ~ l3_lattices(X3)
% 1.71/1.04      | v2_struct_0(X1)
% 1.71/1.04      | X1 != X3 ),
% 1.71/1.04      inference(resolution_lifted,[status(thm)],[c_21,c_18]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_454,plain,
% 1.71/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.71/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.71/1.04      | m1_subset_1(k2_lattices(X1,X0,X2),u1_struct_0(X1))
% 1.71/1.04      | ~ l3_lattices(X1)
% 1.71/1.04      | v2_struct_0(X1) ),
% 1.71/1.04      inference(unflattening,[status(thm)],[c_453]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_943,plain,
% 1.71/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.71/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.71/1.04      | m1_subset_1(k2_lattices(X1,X0,X2),u1_struct_0(X1))
% 1.71/1.04      | ~ l3_lattices(X1)
% 1.71/1.04      | sK5 != X1 ),
% 1.71/1.04      inference(resolution_lifted,[status(thm)],[c_454,c_35]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_944,plain,
% 1.71/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.71/1.04      | m1_subset_1(k2_lattices(sK5,X0,X1),u1_struct_0(sK5))
% 1.71/1.04      | ~ l3_lattices(sK5) ),
% 1.71/1.04      inference(unflattening,[status(thm)],[c_943]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_948,plain,
% 1.71/1.04      ( m1_subset_1(k2_lattices(sK5,X0,X1),u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 1.71/1.04      inference(global_propositional_subsumption,
% 1.71/1.04                [status(thm)],
% 1.71/1.04                [c_944,c_32]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_949,plain,
% 1.71/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.71/1.04      | m1_subset_1(k2_lattices(sK5,X0,X1),u1_struct_0(sK5)) ),
% 1.71/1.04      inference(renaming,[status(thm)],[c_948]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1135,plain,
% 1.71/1.04      ( ~ m1_subset_1(X0_54,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(X1_54,u1_struct_0(sK5))
% 1.71/1.04      | m1_subset_1(k2_lattices(sK5,X0_54,X1_54),u1_struct_0(sK5)) ),
% 1.71/1.04      inference(subtyping,[status(esa)],[c_949]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_2033,plain,
% 1.71/1.04      ( m1_subset_1(k2_lattices(sK5,k6_lattices(sK5),sK6),u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_1135]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1627,plain,
% 1.71/1.04      ( m1_subset_1(X0_54,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(k2_lattices(sK5,X1_54,X2_54),u1_struct_0(sK5))
% 1.71/1.04      | X0_54 != k2_lattices(sK5,X1_54,X2_54) ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_1156]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1674,plain,
% 1.71/1.04      ( m1_subset_1(k4_lattices(sK5,k6_lattices(sK5),sK6),u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(k2_lattices(sK5,X0_54,X1_54),u1_struct_0(sK5))
% 1.71/1.04      | k4_lattices(sK5,k6_lattices(sK5),sK6) != k2_lattices(sK5,X0_54,X1_54) ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_1627]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1988,plain,
% 1.71/1.04      ( m1_subset_1(k4_lattices(sK5,k6_lattices(sK5),sK6),u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(k2_lattices(sK5,k6_lattices(sK5),sK6),u1_struct_0(sK5))
% 1.71/1.04      | k4_lattices(sK5,k6_lattices(sK5),sK6) != k2_lattices(sK5,k6_lattices(sK5),sK6) ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_1674]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1931,plain,
% 1.71/1.04      ( ~ m1_subset_1(X0_54,u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(k2_lattices(sK5,k6_lattices(sK5),sK6),u1_struct_0(sK5))
% 1.71/1.04      | k2_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),X0_54)) = k2_lattices(sK5,k6_lattices(sK5),sK6) ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_1134]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_1934,plain,
% 1.71/1.04      ( ~ m1_subset_1(k2_lattices(sK5,k6_lattices(sK5),sK6),u1_struct_0(sK5))
% 1.71/1.04      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 1.71/1.04      | k2_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),k1_lattices(sK5,k2_lattices(sK5,k6_lattices(sK5),sK6),sK6)) = k2_lattices(sK5,k6_lattices(sK5),sK6) ),
% 1.71/1.04      inference(instantiation,[status(thm)],[c_1931]) ).
% 1.71/1.04  
% 1.71/1.04  cnf(c_4,plain,
% 1.71/1.04      ( v4_lattices(X0)
% 1.71/1.04      | ~ l3_lattices(X0)
% 1.71/1.04      | v2_struct_0(X0)
% 1.71/1.04      | ~ v10_lattices(X0) ),
% 1.71/1.04      inference(cnf_transformation,[],[f64]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_28,plain,
% 1.71/1.05      ( ~ r1_lattices(X0,X1,X2)
% 1.71/1.05      | ~ r1_lattices(X0,X2,X1)
% 1.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.71/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.71/1.05      | ~ l2_lattices(X0)
% 1.71/1.05      | ~ v4_lattices(X0)
% 1.71/1.05      | v2_struct_0(X0)
% 1.71/1.05      | X2 = X1 ),
% 1.71/1.05      inference(cnf_transformation,[],[f91]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_385,plain,
% 1.71/1.05      ( ~ r1_lattices(X0,X1,X2)
% 1.71/1.05      | ~ r1_lattices(X0,X2,X1)
% 1.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.71/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.71/1.05      | ~ l2_lattices(X0)
% 1.71/1.05      | ~ l3_lattices(X0)
% 1.71/1.05      | v2_struct_0(X0)
% 1.71/1.05      | ~ v10_lattices(X0)
% 1.71/1.05      | X2 = X1 ),
% 1.71/1.05      inference(resolution,[status(thm)],[c_4,c_28]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_389,plain,
% 1.71/1.05      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.71/1.05      | ~ r1_lattices(X0,X2,X1)
% 1.71/1.05      | ~ r1_lattices(X0,X1,X2)
% 1.71/1.05      | ~ l3_lattices(X0)
% 1.71/1.05      | v2_struct_0(X0)
% 1.71/1.05      | ~ v10_lattices(X0)
% 1.71/1.05      | X2 = X1 ),
% 1.71/1.05      inference(global_propositional_subsumption,
% 1.71/1.05                [status(thm)],
% 1.71/1.05                [c_385,c_20]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_390,plain,
% 1.71/1.05      ( ~ r1_lattices(X0,X1,X2)
% 1.71/1.05      | ~ r1_lattices(X0,X2,X1)
% 1.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.71/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.71/1.05      | ~ l3_lattices(X0)
% 1.71/1.05      | v2_struct_0(X0)
% 1.71/1.05      | ~ v10_lattices(X0)
% 1.71/1.05      | X2 = X1 ),
% 1.71/1.05      inference(renaming,[status(thm)],[c_389]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_672,plain,
% 1.71/1.05      ( ~ r1_lattices(X0,X1,X2)
% 1.71/1.05      | ~ r1_lattices(X0,X2,X1)
% 1.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.71/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.71/1.05      | ~ l3_lattices(X0)
% 1.71/1.05      | v2_struct_0(X0)
% 1.71/1.05      | X2 = X1
% 1.71/1.05      | sK5 != X0 ),
% 1.71/1.05      inference(resolution_lifted,[status(thm)],[c_390,c_34]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_673,plain,
% 1.71/1.05      ( ~ r1_lattices(sK5,X0,X1)
% 1.71/1.05      | ~ r1_lattices(sK5,X1,X0)
% 1.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.71/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.71/1.05      | ~ l3_lattices(sK5)
% 1.71/1.05      | v2_struct_0(sK5)
% 1.71/1.05      | X1 = X0 ),
% 1.71/1.05      inference(unflattening,[status(thm)],[c_672]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_677,plain,
% 1.71/1.05      ( ~ r1_lattices(sK5,X0,X1)
% 1.71/1.05      | ~ r1_lattices(sK5,X1,X0)
% 1.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.71/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.71/1.05      | X1 = X0 ),
% 1.71/1.05      inference(global_propositional_subsumption,
% 1.71/1.05                [status(thm)],
% 1.71/1.05                [c_673,c_35,c_32]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_678,plain,
% 1.71/1.05      ( ~ r1_lattices(sK5,X0,X1)
% 1.71/1.05      | ~ r1_lattices(sK5,X1,X0)
% 1.71/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.71/1.05      | X1 = X0 ),
% 1.71/1.05      inference(renaming,[status(thm)],[c_677]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_1141,plain,
% 1.71/1.05      ( ~ r1_lattices(sK5,X0_54,X1_54)
% 1.71/1.05      | ~ r1_lattices(sK5,X1_54,X0_54)
% 1.71/1.05      | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
% 1.71/1.05      | ~ m1_subset_1(X1_54,u1_struct_0(sK5))
% 1.71/1.05      | X1_54 = X0_54 ),
% 1.71/1.05      inference(subtyping,[status(esa)],[c_678]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_1689,plain,
% 1.71/1.05      ( ~ r1_lattices(sK5,k4_lattices(sK5,k6_lattices(sK5),sK6),sK6)
% 1.71/1.05      | ~ r1_lattices(sK5,sK6,k4_lattices(sK5,k6_lattices(sK5),sK6))
% 1.71/1.05      | ~ m1_subset_1(k4_lattices(sK5,k6_lattices(sK5),sK6),u1_struct_0(sK5))
% 1.71/1.05      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 1.71/1.05      | sK6 = k4_lattices(sK5,k6_lattices(sK5),sK6) ),
% 1.71/1.05      inference(instantiation,[status(thm)],[c_1141]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_1153,plain,( X0_54 = X0_54 ),theory(equality) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_1655,plain,
% 1.71/1.05      ( k4_lattices(sK5,k6_lattices(sK5),sK6) = k4_lattices(sK5,k6_lattices(sK5),sK6) ),
% 1.71/1.05      inference(instantiation,[status(thm)],[c_1153]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_1620,plain,
% 1.71/1.05      ( k4_lattices(sK5,k6_lattices(sK5),sK6) != X0_54
% 1.71/1.05      | k4_lattices(sK5,k6_lattices(sK5),sK6) = sK6
% 1.71/1.05      | sK6 != X0_54 ),
% 1.71/1.05      inference(instantiation,[status(thm)],[c_1154]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_1654,plain,
% 1.71/1.05      ( k4_lattices(sK5,k6_lattices(sK5),sK6) != k4_lattices(sK5,k6_lattices(sK5),sK6)
% 1.71/1.05      | k4_lattices(sK5,k6_lattices(sK5),sK6) = sK6
% 1.71/1.05      | sK6 != k4_lattices(sK5,k6_lattices(sK5),sK6) ),
% 1.71/1.05      inference(instantiation,[status(thm)],[c_1620]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_22,plain,
% 1.71/1.05      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.71/1.05      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.71/1.05      | ~ l1_lattices(X1)
% 1.71/1.05      | ~ v6_lattices(X1)
% 1.71/1.05      | v2_struct_0(X1)
% 1.71/1.05      | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2) ),
% 1.71/1.05      inference(cnf_transformation,[],[f85]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_429,plain,
% 1.71/1.05      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.71/1.05      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.71/1.05      | ~ v6_lattices(X1)
% 1.71/1.05      | ~ l3_lattices(X3)
% 1.71/1.05      | v2_struct_0(X1)
% 1.71/1.05      | X1 != X3
% 1.71/1.05      | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2) ),
% 1.71/1.05      inference(resolution_lifted,[status(thm)],[c_21,c_22]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_430,plain,
% 1.71/1.05      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.71/1.05      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.71/1.05      | ~ v6_lattices(X1)
% 1.71/1.05      | ~ l3_lattices(X1)
% 1.71/1.05      | v2_struct_0(X1)
% 1.71/1.05      | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2) ),
% 1.71/1.05      inference(unflattening,[status(thm)],[c_429]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_3,plain,
% 1.71/1.05      ( v6_lattices(X0)
% 1.71/1.05      | ~ l3_lattices(X0)
% 1.71/1.05      | v2_struct_0(X0)
% 1.71/1.05      | ~ v10_lattices(X0) ),
% 1.71/1.05      inference(cnf_transformation,[],[f65]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_699,plain,
% 1.71/1.05      ( v6_lattices(X0)
% 1.71/1.05      | ~ l3_lattices(X0)
% 1.71/1.05      | v2_struct_0(X0)
% 1.71/1.05      | sK5 != X0 ),
% 1.71/1.05      inference(resolution_lifted,[status(thm)],[c_3,c_34]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_700,plain,
% 1.71/1.05      ( v6_lattices(sK5) | ~ l3_lattices(sK5) | v2_struct_0(sK5) ),
% 1.71/1.05      inference(unflattening,[status(thm)],[c_699]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_118,plain,
% 1.71/1.05      ( v6_lattices(sK5)
% 1.71/1.05      | ~ l3_lattices(sK5)
% 1.71/1.05      | v2_struct_0(sK5)
% 1.71/1.05      | ~ v10_lattices(sK5) ),
% 1.71/1.05      inference(instantiation,[status(thm)],[c_3]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_702,plain,
% 1.71/1.05      ( v6_lattices(sK5) ),
% 1.71/1.05      inference(global_propositional_subsumption,
% 1.71/1.05                [status(thm)],
% 1.71/1.05                [c_700,c_35,c_34,c_32,c_118]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_817,plain,
% 1.71/1.05      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.71/1.05      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.71/1.05      | ~ l3_lattices(X1)
% 1.71/1.05      | v2_struct_0(X1)
% 1.71/1.05      | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2)
% 1.71/1.05      | sK5 != X1 ),
% 1.71/1.05      inference(resolution_lifted,[status(thm)],[c_430,c_702]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_818,plain,
% 1.71/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.71/1.05      | ~ l3_lattices(sK5)
% 1.71/1.05      | v2_struct_0(sK5)
% 1.71/1.05      | k4_lattices(sK5,X0,X1) = k2_lattices(sK5,X0,X1) ),
% 1.71/1.05      inference(unflattening,[status(thm)],[c_817]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_822,plain,
% 1.71/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.71/1.05      | k4_lattices(sK5,X0,X1) = k2_lattices(sK5,X0,X1) ),
% 1.71/1.05      inference(global_propositional_subsumption,
% 1.71/1.05                [status(thm)],
% 1.71/1.05                [c_818,c_35,c_32]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_1140,plain,
% 1.71/1.05      ( ~ m1_subset_1(X0_54,u1_struct_0(sK5))
% 1.71/1.05      | ~ m1_subset_1(X1_54,u1_struct_0(sK5))
% 1.71/1.05      | k4_lattices(sK5,X0_54,X1_54) = k2_lattices(sK5,X0_54,X1_54) ),
% 1.71/1.05      inference(subtyping,[status(esa)],[c_822]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_1648,plain,
% 1.71/1.05      ( ~ m1_subset_1(k6_lattices(sK5),u1_struct_0(sK5))
% 1.71/1.05      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 1.71/1.05      | k4_lattices(sK5,k6_lattices(sK5),sK6) = k2_lattices(sK5,k6_lattices(sK5),sK6) ),
% 1.71/1.05      inference(instantiation,[status(thm)],[c_1140]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_27,plain,
% 1.71/1.05      ( ~ r1_lattices(X0,X1,X2)
% 1.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.71/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.71/1.05      | ~ v8_lattices(X0)
% 1.71/1.05      | ~ l3_lattices(X0)
% 1.71/1.05      | v2_struct_0(X0)
% 1.71/1.05      | ~ v9_lattices(X0)
% 1.71/1.05      | k2_lattices(X0,X1,X2) = X1 ),
% 1.71/1.05      inference(cnf_transformation,[],[f89]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_887,plain,
% 1.71/1.05      ( ~ r1_lattices(X0,X1,X2)
% 1.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.71/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.71/1.05      | ~ v8_lattices(X0)
% 1.71/1.05      | ~ l3_lattices(X0)
% 1.71/1.05      | ~ v9_lattices(X0)
% 1.71/1.05      | k2_lattices(X0,X1,X2) = X1
% 1.71/1.05      | sK5 != X0 ),
% 1.71/1.05      inference(resolution_lifted,[status(thm)],[c_27,c_35]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_888,plain,
% 1.71/1.05      ( ~ r1_lattices(sK5,X0,X1)
% 1.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.71/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.71/1.05      | ~ v8_lattices(sK5)
% 1.71/1.05      | ~ l3_lattices(sK5)
% 1.71/1.05      | ~ v9_lattices(sK5)
% 1.71/1.05      | k2_lattices(sK5,X0,X1) = X0 ),
% 1.71/1.05      inference(unflattening,[status(thm)],[c_887]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_892,plain,
% 1.71/1.05      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.71/1.05      | ~ r1_lattices(sK5,X0,X1)
% 1.71/1.05      | k2_lattices(sK5,X0,X1) = X0 ),
% 1.71/1.05      inference(global_propositional_subsumption,
% 1.71/1.05                [status(thm)],
% 1.71/1.05                [c_888,c_35,c_34,c_32,c_124,c_127]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_893,plain,
% 1.71/1.05      ( ~ r1_lattices(sK5,X0,X1)
% 1.71/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.71/1.05      | k2_lattices(sK5,X0,X1) = X0 ),
% 1.71/1.05      inference(renaming,[status(thm)],[c_892]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_1137,plain,
% 1.71/1.05      ( ~ r1_lattices(sK5,X0_54,X1_54)
% 1.71/1.05      | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
% 1.71/1.05      | ~ m1_subset_1(X1_54,u1_struct_0(sK5))
% 1.71/1.05      | k2_lattices(sK5,X0_54,X1_54) = X0_54 ),
% 1.71/1.05      inference(subtyping,[status(esa)],[c_893]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_1196,plain,
% 1.71/1.05      ( ~ r1_lattices(sK5,sK6,sK6)
% 1.71/1.05      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 1.71/1.05      | k2_lattices(sK5,sK6,sK6) = sK6 ),
% 1.71/1.05      inference(instantiation,[status(thm)],[c_1137]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_25,plain,
% 1.71/1.05      ( r3_lattices(X0,X1,X1)
% 1.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.71/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.71/1.05      | ~ v6_lattices(X0)
% 1.71/1.05      | ~ v8_lattices(X0)
% 1.71/1.05      | ~ l3_lattices(X0)
% 1.71/1.05      | v2_struct_0(X0)
% 1.71/1.05      | ~ v9_lattices(X0) ),
% 1.71/1.05      inference(cnf_transformation,[],[f88]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_750,plain,
% 1.71/1.05      ( r3_lattices(X0,X1,X1)
% 1.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.71/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.71/1.05      | ~ v8_lattices(X0)
% 1.71/1.05      | ~ l3_lattices(X0)
% 1.71/1.05      | v2_struct_0(X0)
% 1.71/1.05      | ~ v9_lattices(X0)
% 1.71/1.05      | sK5 != X0 ),
% 1.71/1.05      inference(resolution_lifted,[status(thm)],[c_25,c_702]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_751,plain,
% 1.71/1.05      ( r3_lattices(sK5,X0,X0)
% 1.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.71/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.71/1.05      | ~ v8_lattices(sK5)
% 1.71/1.05      | ~ l3_lattices(sK5)
% 1.71/1.05      | v2_struct_0(sK5)
% 1.71/1.05      | ~ v9_lattices(sK5) ),
% 1.71/1.05      inference(unflattening,[status(thm)],[c_750]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_755,plain,
% 1.71/1.05      ( r3_lattices(sK5,X0,X0)
% 1.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.71/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 1.71/1.05      inference(global_propositional_subsumption,
% 1.71/1.05                [status(thm)],
% 1.71/1.05                [c_751,c_35,c_34,c_32,c_124,c_127]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_756,plain,
% 1.71/1.05      ( r3_lattices(sK5,X0,X0)
% 1.71/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
% 1.71/1.05      inference(renaming,[status(thm)],[c_755]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_24,plain,
% 1.71/1.05      ( r1_lattices(X0,X1,X2)
% 1.71/1.05      | ~ r3_lattices(X0,X1,X2)
% 1.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.71/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.71/1.05      | ~ v6_lattices(X0)
% 1.71/1.05      | ~ v8_lattices(X0)
% 1.71/1.05      | ~ l3_lattices(X0)
% 1.71/1.05      | v2_struct_0(X0)
% 1.71/1.05      | ~ v9_lattices(X0) ),
% 1.71/1.05      inference(cnf_transformation,[],[f86]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_771,plain,
% 1.71/1.05      ( r1_lattices(X0,X1,X2)
% 1.71/1.05      | ~ r3_lattices(X0,X1,X2)
% 1.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.71/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.71/1.05      | ~ v8_lattices(X0)
% 1.71/1.05      | ~ l3_lattices(X0)
% 1.71/1.05      | v2_struct_0(X0)
% 1.71/1.05      | ~ v9_lattices(X0)
% 1.71/1.05      | sK5 != X0 ),
% 1.71/1.05      inference(resolution_lifted,[status(thm)],[c_24,c_702]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_772,plain,
% 1.71/1.05      ( r1_lattices(sK5,X0,X1)
% 1.71/1.05      | ~ r3_lattices(sK5,X0,X1)
% 1.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.71/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.71/1.05      | ~ v8_lattices(sK5)
% 1.71/1.05      | ~ l3_lattices(sK5)
% 1.71/1.05      | v2_struct_0(sK5)
% 1.71/1.05      | ~ v9_lattices(sK5) ),
% 1.71/1.05      inference(unflattening,[status(thm)],[c_771]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_776,plain,
% 1.71/1.05      ( r1_lattices(sK5,X0,X1)
% 1.71/1.05      | ~ r3_lattices(sK5,X0,X1)
% 1.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.71/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 1.71/1.05      inference(global_propositional_subsumption,
% 1.71/1.05                [status(thm)],
% 1.71/1.05                [c_772,c_35,c_34,c_32,c_124,c_127]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_777,plain,
% 1.71/1.05      ( r1_lattices(sK5,X0,X1)
% 1.71/1.05      | ~ r3_lattices(sK5,X0,X1)
% 1.71/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
% 1.71/1.05      inference(renaming,[status(thm)],[c_776]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_857,plain,
% 1.71/1.05      ( r1_lattices(sK5,X0,X1)
% 1.71/1.05      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 1.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.71/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.71/1.05      | ~ m1_subset_1(X3,u1_struct_0(sK5))
% 1.71/1.05      | X0 != X2
% 1.71/1.05      | X1 != X2
% 1.71/1.05      | sK5 != sK5 ),
% 1.71/1.05      inference(resolution_lifted,[status(thm)],[c_756,c_777]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_858,plain,
% 1.71/1.05      ( r1_lattices(sK5,X0,X0)
% 1.71/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.71/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 1.71/1.05      inference(unflattening,[status(thm)],[c_857]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_1139,plain,
% 1.71/1.05      ( r1_lattices(sK5,X0_54,X0_54)
% 1.71/1.05      | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
% 1.71/1.05      | ~ m1_subset_1(X1_54,u1_struct_0(sK5)) ),
% 1.71/1.05      inference(subtyping,[status(esa)],[c_858]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_1149,plain,
% 1.71/1.05      ( ~ m1_subset_1(X0_54,u1_struct_0(sK5)) | ~ sP0_iProver_split ),
% 1.71/1.05      inference(splitting,
% 1.71/1.05                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.71/1.05                [c_1139]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_1192,plain,
% 1.71/1.05      ( ~ m1_subset_1(sK6,u1_struct_0(sK5)) | ~ sP0_iProver_split ),
% 1.71/1.05      inference(instantiation,[status(thm)],[c_1149]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_1150,plain,
% 1.71/1.05      ( r1_lattices(sK5,X0_54,X0_54)
% 1.71/1.05      | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
% 1.71/1.05      | ~ sP1_iProver_split ),
% 1.71/1.05      inference(splitting,
% 1.71/1.05                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.71/1.05                [c_1139]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_1189,plain,
% 1.71/1.05      ( r1_lattices(sK5,sK6,sK6)
% 1.71/1.05      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 1.71/1.05      | ~ sP1_iProver_split ),
% 1.71/1.05      inference(instantiation,[status(thm)],[c_1150]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_1151,plain,
% 1.71/1.05      ( sP1_iProver_split | sP0_iProver_split ),
% 1.71/1.05      inference(splitting,
% 1.71/1.05                [splitting(split),new_symbols(definition,[])],
% 1.71/1.05                [c_1139]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_30,negated_conjecture,
% 1.71/1.05      ( k4_lattices(sK5,k6_lattices(sK5),sK6) != sK6 ),
% 1.71/1.05      inference(cnf_transformation,[],[f98]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_1148,negated_conjecture,
% 1.71/1.05      ( k4_lattices(sK5,k6_lattices(sK5),sK6) != sK6 ),
% 1.71/1.05      inference(subtyping,[status(esa)],[c_30]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_1166,plain,
% 1.71/1.05      ( sK6 = sK6 ),
% 1.71/1.05      inference(instantiation,[status(thm)],[c_1153]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(c_40,plain,
% 1.71/1.05      ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
% 1.71/1.05      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 1.71/1.05  
% 1.71/1.05  cnf(contradiction,plain,
% 1.71/1.05      ( $false ),
% 1.71/1.05      inference(minisat,
% 1.71/1.05                [status(thm)],
% 1.71/1.05                [c_12833,c_9861,c_5793,c_4434,c_2904,c_2865,c_2419,
% 1.71/1.05                 c_2179,c_2065,c_2033,c_1988,c_1934,c_1689,c_1655,c_1654,
% 1.71/1.05                 c_1648,c_1196,c_1192,c_1189,c_1151,c_1148,c_1166,c_72,
% 1.71/1.05                 c_69,c_40,c_31,c_32,c_35]) ).
% 1.71/1.05  
% 1.71/1.05  
% 1.71/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 1.71/1.05  
% 1.71/1.05  ------                               Statistics
% 1.71/1.05  
% 1.71/1.05  ------ General
% 1.71/1.05  
% 1.71/1.05  abstr_ref_over_cycles:                  0
% 1.71/1.05  abstr_ref_under_cycles:                 0
% 1.71/1.05  gc_basic_clause_elim:                   0
% 1.71/1.05  forced_gc_time:                         0
% 1.71/1.05  parsing_time:                           0.012
% 1.71/1.05  unif_index_cands_time:                  0.
% 1.71/1.05  unif_index_add_time:                    0.
% 1.71/1.05  orderings_time:                         0.
% 1.71/1.05  out_proof_time:                         0.015
% 1.71/1.05  total_time:                             0.408
% 1.71/1.05  num_of_symbols:                         59
% 1.71/1.05  num_of_terms:                           11975
% 1.71/1.05  
% 1.71/1.05  ------ Preprocessing
% 1.71/1.05  
% 1.71/1.05  num_of_splits:                          2
% 1.71/1.05  num_of_split_atoms:                     2
% 1.71/1.05  num_of_reused_defs:                     0
% 1.71/1.05  num_eq_ax_congr_red:                    31
% 1.71/1.05  num_of_sem_filtered_clauses:            3
% 1.71/1.05  num_of_subtypes:                        3
% 1.71/1.05  monotx_restored_types:                  0
% 1.71/1.05  sat_num_of_epr_types:                   0
% 1.71/1.05  sat_num_of_non_cyclic_types:            0
% 1.71/1.05  sat_guarded_non_collapsed_types:        1
% 1.71/1.05  num_pure_diseq_elim:                    0
% 1.71/1.05  simp_replaced_by:                       0
% 1.71/1.05  res_preprocessed:                       100
% 1.71/1.05  prep_upred:                             0
% 1.71/1.05  prep_unflattend:                        29
% 1.71/1.05  smt_new_axioms:                         0
% 1.71/1.05  pred_elim_cands:                        2
% 1.71/1.05  pred_elim:                              12
% 1.71/1.05  pred_elim_cl:                           19
% 1.71/1.05  pred_elim_cycles:                       14
% 1.71/1.05  merged_defs:                            0
% 1.71/1.05  merged_defs_ncl:                        0
% 1.71/1.05  bin_hyper_res:                          0
% 1.71/1.05  prep_cycles:                            4
% 1.71/1.05  pred_elim_time:                         0.013
% 1.71/1.05  splitting_time:                         0.
% 1.71/1.05  sem_filter_time:                        0.
% 1.71/1.05  monotx_time:                            0.
% 1.71/1.05  subtype_inf_time:                       0.
% 1.71/1.05  
% 1.71/1.05  ------ Problem properties
% 1.71/1.05  
% 1.71/1.05  clauses:                                18
% 1.71/1.05  conjectures:                            2
% 1.71/1.05  epr:                                    1
% 1.71/1.05  horn:                                   16
% 1.71/1.05  ground:                                 4
% 1.71/1.05  unary:                                  3
% 1.71/1.05  binary:                                 4
% 1.71/1.05  lits:                                   51
% 1.71/1.05  lits_eq:                                13
% 1.71/1.05  fd_pure:                                0
% 1.71/1.05  fd_pseudo:                              0
% 1.71/1.05  fd_cond:                                2
% 1.71/1.05  fd_pseudo_cond:                         1
% 1.71/1.05  ac_symbols:                             0
% 1.71/1.05  
% 1.71/1.05  ------ Propositional Solver
% 1.71/1.05  
% 1.71/1.05  prop_solver_calls:                      31
% 1.71/1.05  prop_fast_solver_calls:                 1229
% 1.71/1.05  smt_solver_calls:                       0
% 1.71/1.05  smt_fast_solver_calls:                  0
% 1.71/1.05  prop_num_of_clauses:                    4532
% 1.71/1.05  prop_preprocess_simplified:             9841
% 1.71/1.05  prop_fo_subsumed:                       77
% 1.71/1.05  prop_solver_time:                       0.
% 1.71/1.05  smt_solver_time:                        0.
% 1.71/1.05  smt_fast_solver_time:                   0.
% 1.71/1.05  prop_fast_solver_time:                  0.
% 1.71/1.05  prop_unsat_core_time:                   0.
% 1.71/1.05  
% 1.71/1.05  ------ QBF
% 1.71/1.05  
% 1.71/1.05  qbf_q_res:                              0
% 1.71/1.05  qbf_num_tautologies:                    0
% 1.71/1.05  qbf_prep_cycles:                        0
% 1.71/1.05  
% 1.71/1.05  ------ BMC1
% 1.71/1.05  
% 1.71/1.05  bmc1_current_bound:                     -1
% 1.71/1.05  bmc1_last_solved_bound:                 -1
% 1.71/1.05  bmc1_unsat_core_size:                   -1
% 1.71/1.05  bmc1_unsat_core_parents_size:           -1
% 1.71/1.05  bmc1_merge_next_fun:                    0
% 1.71/1.05  bmc1_unsat_core_clauses_time:           0.
% 1.71/1.05  
% 1.71/1.05  ------ Instantiation
% 1.71/1.05  
% 1.71/1.05  inst_num_of_clauses:                    1500
% 1.71/1.05  inst_num_in_passive:                    208
% 1.71/1.05  inst_num_in_active:                     613
% 1.71/1.05  inst_num_in_unprocessed:                678
% 1.71/1.05  inst_num_of_loops:                      691
% 1.71/1.05  inst_num_of_learning_restarts:          0
% 1.71/1.05  inst_num_moves_active_passive:          73
% 1.71/1.05  inst_lit_activity:                      0
% 1.71/1.05  inst_lit_activity_moves:                0
% 1.71/1.05  inst_num_tautologies:                   0
% 1.71/1.05  inst_num_prop_implied:                  0
% 1.71/1.05  inst_num_existing_simplified:           0
% 1.71/1.05  inst_num_eq_res_simplified:             0
% 1.71/1.05  inst_num_child_elim:                    0
% 1.71/1.05  inst_num_of_dismatching_blockings:      997
% 1.71/1.05  inst_num_of_non_proper_insts:           1916
% 1.71/1.05  inst_num_of_duplicates:                 0
% 1.71/1.05  inst_inst_num_from_inst_to_res:         0
% 1.71/1.05  inst_dismatching_checking_time:         0.
% 1.71/1.05  
% 1.71/1.05  ------ Resolution
% 1.71/1.05  
% 1.71/1.05  res_num_of_clauses:                     0
% 1.71/1.05  res_num_in_passive:                     0
% 1.71/1.05  res_num_in_active:                      0
% 1.71/1.05  res_num_of_loops:                       104
% 1.71/1.05  res_forward_subset_subsumed:            174
% 1.71/1.05  res_backward_subset_subsumed:           0
% 1.71/1.05  res_forward_subsumed:                   0
% 1.71/1.05  res_backward_subsumed:                  0
% 1.71/1.05  res_forward_subsumption_resolution:     0
% 1.71/1.05  res_backward_subsumption_resolution:    0
% 1.71/1.05  res_clause_to_clause_subsumption:       1830
% 1.71/1.05  res_orphan_elimination:                 0
% 1.71/1.05  res_tautology_del:                      139
% 1.71/1.05  res_num_eq_res_simplified:              0
% 1.71/1.05  res_num_sel_changes:                    0
% 1.71/1.05  res_moves_from_active_to_pass:          0
% 1.71/1.05  
% 1.71/1.05  ------ Superposition
% 1.71/1.05  
% 1.71/1.05  sup_time_total:                         0.
% 1.71/1.05  sup_time_generating:                    0.
% 1.71/1.05  sup_time_sim_full:                      0.
% 1.71/1.05  sup_time_sim_immed:                     0.
% 1.71/1.05  
% 1.71/1.05  sup_num_of_clauses:                     283
% 1.71/1.05  sup_num_in_active:                      132
% 1.71/1.05  sup_num_in_passive:                     151
% 1.71/1.05  sup_num_of_loops:                       138
% 1.71/1.05  sup_fw_superposition:                   286
% 1.71/1.05  sup_bw_superposition:                   69
% 1.71/1.05  sup_immediate_simplified:               48
% 1.71/1.05  sup_given_eliminated:                   0
% 1.71/1.05  comparisons_done:                       0
% 1.71/1.05  comparisons_avoided:                    10
% 1.71/1.05  
% 1.71/1.05  ------ Simplifications
% 1.71/1.05  
% 1.71/1.05  
% 1.71/1.05  sim_fw_subset_subsumed:                 16
% 1.71/1.05  sim_bw_subset_subsumed:                 0
% 1.71/1.05  sim_fw_subsumed:                        2
% 1.71/1.05  sim_bw_subsumed:                        0
% 1.71/1.05  sim_fw_subsumption_res:                 0
% 1.71/1.05  sim_bw_subsumption_res:                 0
% 1.71/1.05  sim_tautology_del:                      11
% 1.71/1.05  sim_eq_tautology_del:                   33
% 1.71/1.05  sim_eq_res_simp:                        0
% 1.71/1.05  sim_fw_demodulated:                     0
% 1.71/1.05  sim_bw_demodulated:                     6
% 1.71/1.05  sim_light_normalised:                   31
% 1.71/1.05  sim_joinable_taut:                      0
% 1.71/1.05  sim_joinable_simp:                      0
% 1.71/1.05  sim_ac_normalised:                      0
% 1.71/1.05  sim_smt_subsumption:                    0
% 1.71/1.05  
%------------------------------------------------------------------------------
