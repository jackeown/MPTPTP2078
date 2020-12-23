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
% DateTime   : Thu Dec  3 12:13:16 EST 2020

% Result     : Theorem 7.02s
% Output     : CNFRefutation 7.02s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 448 expanded)
%              Number of clauses        :   85 ( 123 expanded)
%              Number of leaves         :   19 ( 114 expanded)
%              Depth                    :   16
%              Number of atoms          :  708 (2368 expanded)
%              Number of equality atoms :  135 ( 388 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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

fof(f24,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k1_lattices(X0,k2_lattices(X0,X1,sK5(X0)),sK5(X0)) != sK5(X0)
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK4(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( k1_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),sK5(X0)) != sK5(X0)
            & m1_subset_1(sK5(X0),u1_struct_0(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f53,f55,f54])).

fof(f78,plain,(
    ! [X4,X0,X3] :
      ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),sK7)
        & m1_subset_1(sK7,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k5_lattices(sK6) != k4_lattices(sK6,k5_lattices(sK6),X1)
          & m1_subset_1(X1,u1_struct_0(sK6)) )
      & l3_lattices(sK6)
      & v13_lattices(sK6)
      & v10_lattices(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( k5_lattices(sK6) != k4_lattices(sK6,k5_lattices(sK6),sK7)
    & m1_subset_1(sK7,u1_struct_0(sK6))
    & l3_lattices(sK6)
    & v13_lattices(sK6)
    & v10_lattices(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f40,f59,f58])).

fof(f94,plain,(
    l3_lattices(sK6) ),
    inference(cnf_transformation,[],[f60])).

fof(f91,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f60])).

fof(f92,plain,(
    v10_lattices(sK6) ),
    inference(cnf_transformation,[],[f60])).

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

fof(f15,plain,(
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

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f65,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

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
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k1_lattices(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f85,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k5_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK0(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK0(X0,X1)) != X1 )
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ( ( k2_lattices(X0,sK0(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK0(X0,X1)) != X1 )
                & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X1,X3) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f98,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f93,plain,(
    v13_lattices(sK6) ),
    inference(cnf_transformation,[],[f60])).

fof(f84,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f83,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f37,plain,(
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
    inference(flattening,[],[f37])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_lattices(X0,X2,X1)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f96,plain,(
    k5_lattices(sK6) != k4_lattices(sK6,k5_lattices(sK6),sK7) ),
    inference(cnf_transformation,[],[f60])).

fof(f95,plain,(
    m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1071,plain,
    ( X0_55 != X1_55
    | X2_55 != X1_55
    | X2_55 = X0_55 ),
    theory(equality)).

cnf(c_2504,plain,
    ( X0_55 != X1_55
    | X0_55 = k2_lattices(sK6,X2_55,X3_55)
    | k2_lattices(sK6,X2_55,X3_55) != X1_55 ),
    inference(instantiation,[status(thm)],[c_1071])).

cnf(c_3987,plain,
    ( X0_55 = k2_lattices(sK6,k5_lattices(sK6),X1_55)
    | X0_55 != k5_lattices(sK6)
    | k2_lattices(sK6,k5_lattices(sK6),X1_55) != k5_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_2504])).

cnf(c_7906,plain,
    ( k2_lattices(sK6,k5_lattices(sK6),X0_55) != k5_lattices(sK6)
    | k5_lattices(sK6) = k2_lattices(sK6,k5_lattices(sK6),X0_55)
    | k5_lattices(sK6) != k5_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_3987])).

cnf(c_16922,plain,
    ( k2_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),sK7)) != k5_lattices(sK6)
    | k5_lattices(sK6) = k2_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),sK7))
    | k5_lattices(sK6) != k5_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_7906])).

cnf(c_1074,plain,
    ( ~ r1_lattices(X0_57,X0_55,X1_55)
    | r1_lattices(X0_57,X2_55,X1_55)
    | X2_55 != X0_55 ),
    theory(equality)).

cnf(c_2391,plain,
    ( ~ r1_lattices(sK6,X0_55,k4_lattices(sK6,k5_lattices(sK6),X1_55))
    | r1_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),X1_55))
    | k5_lattices(sK6) != X0_55 ),
    inference(instantiation,[status(thm)],[c_1074])).

cnf(c_5240,plain,
    ( ~ r1_lattices(sK6,k2_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),sK7)),k4_lattices(sK6,k5_lattices(sK6),sK7))
    | r1_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),sK7))
    | k5_lattices(sK6) != k2_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),sK7)) ),
    inference(instantiation,[status(thm)],[c_2391])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X0,X2),X2) = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_32,negated_conjecture,
    ( l3_lattices(sK6) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_834,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X0,X2),X2) = X2
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_32])).

cnf(c_835,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ v8_lattices(sK6)
    | v2_struct_0(sK6)
    | k1_lattices(sK6,k2_lattices(sK6,X1,X0),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_834])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_34,negated_conjecture,
    ( v10_lattices(sK6) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_124,plain,
    ( v8_lattices(sK6)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ v10_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_839,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | k1_lattices(sK6,k2_lattices(sK6,X1,X0),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_835,c_35,c_34,c_32,c_124])).

cnf(c_840,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | k1_lattices(sK6,k2_lattices(sK6,X0,X1),X1) = X1 ),
    inference(renaming,[status(thm)],[c_839])).

cnf(c_1054,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK6))
    | k1_lattices(sK6,k2_lattices(sK6,X0_55,X1_55),X1_55) = X1_55 ),
    inference(subtyping,[status(esa)],[c_840])).

cnf(c_1684,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK6))
    | ~ m1_subset_1(k4_lattices(sK6,k5_lattices(sK6),sK7),u1_struct_0(sK6))
    | k1_lattices(sK6,k2_lattices(sK6,X0_55,k4_lattices(sK6,k5_lattices(sK6),sK7)),k4_lattices(sK6,k5_lattices(sK6),sK7)) = k4_lattices(sK6,k5_lattices(sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_1054])).

cnf(c_2955,plain,
    ( ~ m1_subset_1(k4_lattices(sK6,k5_lattices(sK6),sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6))
    | k1_lattices(sK6,k2_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),sK7)),k4_lattices(sK6,k5_lattices(sK6),sK7)) = k4_lattices(sK6,k5_lattices(sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_1684])).

cnf(c_10,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) != X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_895,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | k1_lattices(X0,X1,X2) != X2
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_35])).

cnf(c_896,plain,
    ( r1_lattices(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ l2_lattices(sK6)
    | k1_lattices(sK6,X0,X1) != X1 ),
    inference(unflattening,[status(thm)],[c_895])).

cnf(c_23,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_60,plain,
    ( l2_lattices(sK6)
    | ~ l3_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_898,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r1_lattices(sK6,X0,X1)
    | k1_lattices(sK6,X0,X1) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_896,c_32,c_60])).

cnf(c_899,plain,
    ( r1_lattices(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | k1_lattices(sK6,X0,X1) != X1 ),
    inference(renaming,[status(thm)],[c_898])).

cnf(c_1052,plain,
    ( r1_lattices(sK6,X0_55,X1_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK6))
    | k1_lattices(sK6,X0_55,X1_55) != X1_55 ),
    inference(subtyping,[status(esa)],[c_899])).

cnf(c_1601,plain,
    ( r1_lattices(sK6,X0_55,k4_lattices(sK6,k5_lattices(sK6),sK7))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK6))
    | ~ m1_subset_1(k4_lattices(sK6,k5_lattices(sK6),sK7),u1_struct_0(sK6))
    | k1_lattices(sK6,X0_55,k4_lattices(sK6,k5_lattices(sK6),sK7)) != k4_lattices(sK6,k5_lattices(sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_1052])).

cnf(c_1683,plain,
    ( r1_lattices(sK6,k2_lattices(sK6,X0_55,k4_lattices(sK6,k5_lattices(sK6),sK7)),k4_lattices(sK6,k5_lattices(sK6),sK7))
    | ~ m1_subset_1(k4_lattices(sK6,k5_lattices(sK6),sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(k2_lattices(sK6,X0_55,k4_lattices(sK6,k5_lattices(sK6),sK7)),u1_struct_0(sK6))
    | k1_lattices(sK6,k2_lattices(sK6,X0_55,k4_lattices(sK6,k5_lattices(sK6),sK7)),k4_lattices(sK6,k5_lattices(sK6),sK7)) != k4_lattices(sK6,k5_lattices(sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_1601])).

cnf(c_2594,plain,
    ( r1_lattices(sK6,k2_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),sK7)),k4_lattices(sK6,k5_lattices(sK6),sK7))
    | ~ m1_subset_1(k4_lattices(sK6,k5_lattices(sK6),sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(k2_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),sK7)),u1_struct_0(sK6))
    | k1_lattices(sK6,k2_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),sK7)),k4_lattices(sK6,k5_lattices(sK6),sK7)) != k4_lattices(sK6,k5_lattices(sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_1683])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_33,negated_conjecture,
    ( v13_lattices(sK6) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_514,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_33])).

cnf(c_515,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6))
    | ~ l1_lattices(sK6)
    | v2_struct_0(sK6)
    | k2_lattices(sK6,k5_lattices(sK6),X0) = k5_lattices(sK6) ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_24,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_57,plain,
    ( l1_lattices(sK6)
    | ~ l3_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_22,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_63,plain,
    ( m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6))
    | ~ l1_lattices(sK6)
    | v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_519,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | k2_lattices(sK6,k5_lattices(sK6),X0) = k5_lattices(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_515,c_35,c_32,c_57,c_63])).

cnf(c_1062,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK6))
    | k2_lattices(sK6,k5_lattices(sK6),X0_55) = k5_lattices(sK6) ),
    inference(subtyping,[status(esa)],[c_519])).

cnf(c_2267,plain,
    ( ~ m1_subset_1(k4_lattices(sK6,k5_lattices(sK6),sK7),u1_struct_0(sK6))
    | k2_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),sK7)) = k5_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_1062])).

cnf(c_1073,plain,
    ( ~ m1_subset_1(X0_55,X0_56)
    | m1_subset_1(X1_55,X0_56)
    | X1_55 != X0_55 ),
    theory(equality)).

cnf(c_1521,plain,
    ( m1_subset_1(X0_55,u1_struct_0(sK6))
    | ~ m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6))
    | X0_55 != k5_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_1073])).

cnf(c_1834,plain,
    ( m1_subset_1(k2_lattices(sK6,X0_55,k4_lattices(sK6,k5_lattices(sK6),sK7)),u1_struct_0(sK6))
    | ~ m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6))
    | k2_lattices(sK6,X0_55,k4_lattices(sK6,k5_lattices(sK6),sK7)) != k5_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_1521])).

cnf(c_2266,plain,
    ( m1_subset_1(k2_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),sK7)),u1_struct_0(sK6))
    | ~ m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6))
    | k2_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),sK7)) != k5_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_1834])).

cnf(c_1070,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_1756,plain,
    ( k5_lattices(sK6) = k5_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_1070])).

cnf(c_28,plain,
    ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_467,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_34])).

cnf(c_468,plain,
    ( v6_lattices(sK6)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_121,plain,
    ( v6_lattices(sK6)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ v10_lattices(sK6) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_470,plain,
    ( v6_lattices(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_468,c_35,c_34,c_32,c_121])).

cnf(c_740,plain,
    ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_470])).

cnf(c_741,plain,
    ( r1_lattices(sK6,k4_lattices(sK6,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ v8_lattices(sK6)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_740])).

cnf(c_745,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r1_lattices(sK6,k4_lattices(sK6,X0,X1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_741,c_35,c_34,c_32,c_124])).

cnf(c_746,plain,
    ( r1_lattices(sK6,k4_lattices(sK6,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_745])).

cnf(c_1058,plain,
    ( r1_lattices(sK6,k4_lattices(sK6,X0_55,X1_55),X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_746])).

cnf(c_1589,plain,
    ( r1_lattices(sK6,k4_lattices(sK6,k5_lattices(sK6),sK7),k5_lattices(sK6))
    | ~ m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_1058])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X0,X2),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_624,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X0,X2),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_21])).

cnf(c_625,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X0,X2),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_624])).

cnf(c_761,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X0,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_625,c_470])).

cnf(c_762,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(k4_lattices(sK6,X1,X0),u1_struct_0(sK6))
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_761])).

cnf(c_766,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(k4_lattices(sK6,X1,X0),u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_762,c_35,c_32])).

cnf(c_767,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(k4_lattices(sK6,X0,X1),u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_766])).

cnf(c_1057,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK6))
    | m1_subset_1(k4_lattices(sK6,X0_55,X1_55),u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_767])).

cnf(c_1541,plain,
    ( m1_subset_1(k4_lattices(sK6,k5_lattices(sK6),sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_1057])).

cnf(c_4,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_29,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | ~ v4_lattices(X0)
    | v2_struct_0(X0)
    | X2 = X1 ),
    inference(cnf_transformation,[],[f90])).

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
    inference(resolution,[status(thm)],[c_4,c_29])).

cnf(c_389,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r1_lattices(X0,X2,X1)
    | ~ r1_lattices(X0,X1,X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | X2 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_385,c_23])).

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

cnf(c_429,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | X2 = X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_390,c_34])).

cnf(c_430,plain,
    ( ~ r1_lattices(sK6,X0,X1)
    | ~ r1_lattices(sK6,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_434,plain,
    ( ~ r1_lattices(sK6,X0,X1)
    | ~ r1_lattices(sK6,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_430,c_35,c_32])).

cnf(c_435,plain,
    ( ~ r1_lattices(sK6,X0,X1)
    | ~ r1_lattices(sK6,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | X0 = X1 ),
    inference(renaming,[status(thm)],[c_434])).

cnf(c_1063,plain,
    ( ~ r1_lattices(sK6,X0_55,X1_55)
    | ~ r1_lattices(sK6,X1_55,X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK6))
    | X0_55 = X1_55 ),
    inference(subtyping,[status(esa)],[c_435])).

cnf(c_1513,plain,
    ( ~ r1_lattices(sK6,k4_lattices(sK6,k5_lattices(sK6),sK7),k5_lattices(sK6))
    | ~ r1_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),sK7))
    | ~ m1_subset_1(k4_lattices(sK6,k5_lattices(sK6),sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6))
    | k5_lattices(sK6) = k4_lattices(sK6,k5_lattices(sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_1063])).

cnf(c_30,negated_conjecture,
    ( k5_lattices(sK6) != k4_lattices(sK6,k5_lattices(sK6),sK7) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1065,negated_conjecture,
    ( k5_lattices(sK6) != k4_lattices(sK6,k5_lattices(sK6),sK7) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f95])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16922,c_5240,c_2955,c_2594,c_2267,c_2266,c_1756,c_1589,c_1541,c_1513,c_1065,c_63,c_57,c_31,c_32,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:10:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.02/1.42  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.02/1.42  
% 7.02/1.42  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.02/1.42  
% 7.02/1.42  ------  iProver source info
% 7.02/1.42  
% 7.02/1.42  git: date: 2020-06-30 10:37:57 +0100
% 7.02/1.42  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.02/1.42  git: non_committed_changes: false
% 7.02/1.42  git: last_make_outside_of_git: false
% 7.02/1.42  
% 7.02/1.42  ------ 
% 7.02/1.42  
% 7.02/1.42  ------ Input Options
% 7.02/1.42  
% 7.02/1.42  --out_options                           all
% 7.02/1.42  --tptp_safe_out                         true
% 7.02/1.42  --problem_path                          ""
% 7.02/1.42  --include_path                          ""
% 7.02/1.42  --clausifier                            res/vclausify_rel
% 7.02/1.42  --clausifier_options                    --mode clausify
% 7.02/1.42  --stdin                                 false
% 7.02/1.42  --stats_out                             all
% 7.02/1.42  
% 7.02/1.42  ------ General Options
% 7.02/1.42  
% 7.02/1.42  --fof                                   false
% 7.02/1.42  --time_out_real                         305.
% 7.02/1.42  --time_out_virtual                      -1.
% 7.02/1.42  --symbol_type_check                     false
% 7.02/1.42  --clausify_out                          false
% 7.02/1.42  --sig_cnt_out                           false
% 7.02/1.42  --trig_cnt_out                          false
% 7.02/1.42  --trig_cnt_out_tolerance                1.
% 7.02/1.42  --trig_cnt_out_sk_spl                   false
% 7.02/1.42  --abstr_cl_out                          false
% 7.02/1.42  
% 7.02/1.42  ------ Global Options
% 7.02/1.42  
% 7.02/1.42  --schedule                              default
% 7.02/1.42  --add_important_lit                     false
% 7.02/1.42  --prop_solver_per_cl                    1000
% 7.02/1.42  --min_unsat_core                        false
% 7.02/1.42  --soft_assumptions                      false
% 7.02/1.42  --soft_lemma_size                       3
% 7.02/1.42  --prop_impl_unit_size                   0
% 7.02/1.42  --prop_impl_unit                        []
% 7.02/1.42  --share_sel_clauses                     true
% 7.02/1.42  --reset_solvers                         false
% 7.02/1.42  --bc_imp_inh                            [conj_cone]
% 7.02/1.42  --conj_cone_tolerance                   3.
% 7.02/1.42  --extra_neg_conj                        none
% 7.02/1.42  --large_theory_mode                     true
% 7.02/1.42  --prolific_symb_bound                   200
% 7.02/1.42  --lt_threshold                          2000
% 7.02/1.42  --clause_weak_htbl                      true
% 7.02/1.42  --gc_record_bc_elim                     false
% 7.02/1.42  
% 7.02/1.42  ------ Preprocessing Options
% 7.02/1.42  
% 7.02/1.42  --preprocessing_flag                    true
% 7.02/1.42  --time_out_prep_mult                    0.1
% 7.02/1.42  --splitting_mode                        input
% 7.02/1.42  --splitting_grd                         true
% 7.02/1.42  --splitting_cvd                         false
% 7.02/1.42  --splitting_cvd_svl                     false
% 7.02/1.42  --splitting_nvd                         32
% 7.02/1.42  --sub_typing                            true
% 7.02/1.42  --prep_gs_sim                           true
% 7.02/1.42  --prep_unflatten                        true
% 7.02/1.42  --prep_res_sim                          true
% 7.02/1.42  --prep_upred                            true
% 7.02/1.42  --prep_sem_filter                       exhaustive
% 7.02/1.42  --prep_sem_filter_out                   false
% 7.02/1.42  --pred_elim                             true
% 7.02/1.42  --res_sim_input                         true
% 7.02/1.42  --eq_ax_congr_red                       true
% 7.02/1.42  --pure_diseq_elim                       true
% 7.02/1.42  --brand_transform                       false
% 7.02/1.42  --non_eq_to_eq                          false
% 7.02/1.42  --prep_def_merge                        true
% 7.02/1.42  --prep_def_merge_prop_impl              false
% 7.02/1.42  --prep_def_merge_mbd                    true
% 7.02/1.42  --prep_def_merge_tr_red                 false
% 7.02/1.42  --prep_def_merge_tr_cl                  false
% 7.02/1.42  --smt_preprocessing                     true
% 7.02/1.42  --smt_ac_axioms                         fast
% 7.02/1.42  --preprocessed_out                      false
% 7.02/1.42  --preprocessed_stats                    false
% 7.02/1.42  
% 7.02/1.42  ------ Abstraction refinement Options
% 7.02/1.42  
% 7.02/1.42  --abstr_ref                             []
% 7.02/1.42  --abstr_ref_prep                        false
% 7.02/1.42  --abstr_ref_until_sat                   false
% 7.02/1.42  --abstr_ref_sig_restrict                funpre
% 7.02/1.42  --abstr_ref_af_restrict_to_split_sk     false
% 7.02/1.42  --abstr_ref_under                       []
% 7.02/1.42  
% 7.02/1.42  ------ SAT Options
% 7.02/1.42  
% 7.02/1.42  --sat_mode                              false
% 7.02/1.42  --sat_fm_restart_options                ""
% 7.02/1.42  --sat_gr_def                            false
% 7.02/1.42  --sat_epr_types                         true
% 7.02/1.42  --sat_non_cyclic_types                  false
% 7.02/1.42  --sat_finite_models                     false
% 7.02/1.42  --sat_fm_lemmas                         false
% 7.02/1.42  --sat_fm_prep                           false
% 7.02/1.42  --sat_fm_uc_incr                        true
% 7.02/1.42  --sat_out_model                         small
% 7.02/1.42  --sat_out_clauses                       false
% 7.02/1.42  
% 7.02/1.42  ------ QBF Options
% 7.02/1.42  
% 7.02/1.42  --qbf_mode                              false
% 7.02/1.42  --qbf_elim_univ                         false
% 7.02/1.42  --qbf_dom_inst                          none
% 7.02/1.42  --qbf_dom_pre_inst                      false
% 7.02/1.42  --qbf_sk_in                             false
% 7.02/1.42  --qbf_pred_elim                         true
% 7.02/1.42  --qbf_split                             512
% 7.02/1.42  
% 7.02/1.42  ------ BMC1 Options
% 7.02/1.42  
% 7.02/1.42  --bmc1_incremental                      false
% 7.02/1.42  --bmc1_axioms                           reachable_all
% 7.02/1.42  --bmc1_min_bound                        0
% 7.02/1.42  --bmc1_max_bound                        -1
% 7.02/1.42  --bmc1_max_bound_default                -1
% 7.02/1.42  --bmc1_symbol_reachability              true
% 7.02/1.42  --bmc1_property_lemmas                  false
% 7.02/1.42  --bmc1_k_induction                      false
% 7.02/1.42  --bmc1_non_equiv_states                 false
% 7.02/1.42  --bmc1_deadlock                         false
% 7.02/1.42  --bmc1_ucm                              false
% 7.02/1.42  --bmc1_add_unsat_core                   none
% 7.02/1.42  --bmc1_unsat_core_children              false
% 7.02/1.42  --bmc1_unsat_core_extrapolate_axioms    false
% 7.02/1.42  --bmc1_out_stat                         full
% 7.02/1.42  --bmc1_ground_init                      false
% 7.02/1.42  --bmc1_pre_inst_next_state              false
% 7.02/1.42  --bmc1_pre_inst_state                   false
% 7.02/1.42  --bmc1_pre_inst_reach_state             false
% 7.02/1.42  --bmc1_out_unsat_core                   false
% 7.02/1.42  --bmc1_aig_witness_out                  false
% 7.02/1.42  --bmc1_verbose                          false
% 7.02/1.42  --bmc1_dump_clauses_tptp                false
% 7.02/1.42  --bmc1_dump_unsat_core_tptp             false
% 7.02/1.42  --bmc1_dump_file                        -
% 7.02/1.42  --bmc1_ucm_expand_uc_limit              128
% 7.02/1.42  --bmc1_ucm_n_expand_iterations          6
% 7.02/1.42  --bmc1_ucm_extend_mode                  1
% 7.02/1.42  --bmc1_ucm_init_mode                    2
% 7.02/1.42  --bmc1_ucm_cone_mode                    none
% 7.02/1.42  --bmc1_ucm_reduced_relation_type        0
% 7.02/1.42  --bmc1_ucm_relax_model                  4
% 7.02/1.42  --bmc1_ucm_full_tr_after_sat            true
% 7.02/1.42  --bmc1_ucm_expand_neg_assumptions       false
% 7.02/1.42  --bmc1_ucm_layered_model                none
% 7.02/1.42  --bmc1_ucm_max_lemma_size               10
% 7.02/1.42  
% 7.02/1.42  ------ AIG Options
% 7.02/1.42  
% 7.02/1.42  --aig_mode                              false
% 7.02/1.42  
% 7.02/1.42  ------ Instantiation Options
% 7.02/1.42  
% 7.02/1.42  --instantiation_flag                    true
% 7.02/1.42  --inst_sos_flag                         false
% 7.02/1.42  --inst_sos_phase                        true
% 7.02/1.42  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.02/1.42  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.02/1.42  --inst_lit_sel_side                     num_symb
% 7.02/1.42  --inst_solver_per_active                1400
% 7.02/1.42  --inst_solver_calls_frac                1.
% 7.02/1.42  --inst_passive_queue_type               priority_queues
% 7.02/1.42  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.02/1.42  --inst_passive_queues_freq              [25;2]
% 7.02/1.42  --inst_dismatching                      true
% 7.02/1.42  --inst_eager_unprocessed_to_passive     true
% 7.02/1.42  --inst_prop_sim_given                   true
% 7.02/1.42  --inst_prop_sim_new                     false
% 7.02/1.42  --inst_subs_new                         false
% 7.02/1.42  --inst_eq_res_simp                      false
% 7.02/1.42  --inst_subs_given                       false
% 7.02/1.42  --inst_orphan_elimination               true
% 7.02/1.42  --inst_learning_loop_flag               true
% 7.02/1.42  --inst_learning_start                   3000
% 7.02/1.42  --inst_learning_factor                  2
% 7.02/1.42  --inst_start_prop_sim_after_learn       3
% 7.02/1.42  --inst_sel_renew                        solver
% 7.02/1.42  --inst_lit_activity_flag                true
% 7.02/1.42  --inst_restr_to_given                   false
% 7.02/1.42  --inst_activity_threshold               500
% 7.02/1.42  --inst_out_proof                        true
% 7.02/1.42  
% 7.02/1.42  ------ Resolution Options
% 7.02/1.42  
% 7.02/1.42  --resolution_flag                       true
% 7.02/1.42  --res_lit_sel                           adaptive
% 7.02/1.42  --res_lit_sel_side                      none
% 7.02/1.42  --res_ordering                          kbo
% 7.02/1.42  --res_to_prop_solver                    active
% 7.02/1.42  --res_prop_simpl_new                    false
% 7.02/1.42  --res_prop_simpl_given                  true
% 7.02/1.42  --res_passive_queue_type                priority_queues
% 7.02/1.42  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.02/1.42  --res_passive_queues_freq               [15;5]
% 7.02/1.42  --res_forward_subs                      full
% 7.02/1.42  --res_backward_subs                     full
% 7.02/1.42  --res_forward_subs_resolution           true
% 7.02/1.42  --res_backward_subs_resolution          true
% 7.02/1.42  --res_orphan_elimination                true
% 7.02/1.42  --res_time_limit                        2.
% 7.02/1.42  --res_out_proof                         true
% 7.02/1.42  
% 7.02/1.42  ------ Superposition Options
% 7.02/1.42  
% 7.02/1.42  --superposition_flag                    true
% 7.02/1.42  --sup_passive_queue_type                priority_queues
% 7.02/1.42  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.02/1.42  --sup_passive_queues_freq               [8;1;4]
% 7.02/1.42  --demod_completeness_check              fast
% 7.02/1.42  --demod_use_ground                      true
% 7.02/1.42  --sup_to_prop_solver                    passive
% 7.02/1.42  --sup_prop_simpl_new                    true
% 7.02/1.42  --sup_prop_simpl_given                  true
% 7.02/1.42  --sup_fun_splitting                     false
% 7.02/1.42  --sup_smt_interval                      50000
% 7.02/1.42  
% 7.02/1.42  ------ Superposition Simplification Setup
% 7.02/1.42  
% 7.02/1.42  --sup_indices_passive                   []
% 7.02/1.42  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.02/1.42  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.02/1.42  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.02/1.42  --sup_full_triv                         [TrivRules;PropSubs]
% 7.02/1.42  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.02/1.42  --sup_full_bw                           [BwDemod]
% 7.02/1.42  --sup_immed_triv                        [TrivRules]
% 7.02/1.42  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.02/1.42  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.02/1.42  --sup_immed_bw_main                     []
% 7.02/1.42  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.02/1.42  --sup_input_triv                        [Unflattening;TrivRules]
% 7.02/1.42  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.02/1.42  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.02/1.42  
% 7.02/1.42  ------ Combination Options
% 7.02/1.42  
% 7.02/1.42  --comb_res_mult                         3
% 7.02/1.42  --comb_sup_mult                         2
% 7.02/1.42  --comb_inst_mult                        10
% 7.02/1.42  
% 7.02/1.42  ------ Debug Options
% 7.02/1.42  
% 7.02/1.42  --dbg_backtrace                         false
% 7.02/1.42  --dbg_dump_prop_clauses                 false
% 7.02/1.42  --dbg_dump_prop_clauses_file            -
% 7.02/1.42  --dbg_out_stat                          false
% 7.02/1.42  ------ Parsing...
% 7.02/1.42  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.02/1.42  
% 7.02/1.42  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 7.02/1.42  
% 7.02/1.42  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.02/1.42  
% 7.02/1.42  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.02/1.42  ------ Proving...
% 7.02/1.42  ------ Problem Properties 
% 7.02/1.42  
% 7.02/1.42  
% 7.02/1.42  clauses                                 17
% 7.02/1.42  conjectures                             2
% 7.02/1.42  EPR                                     1
% 7.02/1.42  Horn                                    15
% 7.02/1.42  unary                                   3
% 7.02/1.42  binary                                  4
% 7.02/1.42  lits                                    47
% 7.02/1.42  lits eq                                 12
% 7.02/1.42  fd_pure                                 0
% 7.02/1.42  fd_pseudo                               0
% 7.02/1.42  fd_cond                                 2
% 7.02/1.42  fd_pseudo_cond                          1
% 7.02/1.42  AC symbols                              0
% 7.02/1.42  
% 7.02/1.42  ------ Schedule dynamic 5 is on 
% 7.02/1.42  
% 7.02/1.42  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.02/1.42  
% 7.02/1.42  
% 7.02/1.42  ------ 
% 7.02/1.42  Current options:
% 7.02/1.42  ------ 
% 7.02/1.42  
% 7.02/1.42  ------ Input Options
% 7.02/1.42  
% 7.02/1.42  --out_options                           all
% 7.02/1.42  --tptp_safe_out                         true
% 7.02/1.42  --problem_path                          ""
% 7.02/1.42  --include_path                          ""
% 7.02/1.42  --clausifier                            res/vclausify_rel
% 7.02/1.42  --clausifier_options                    --mode clausify
% 7.02/1.42  --stdin                                 false
% 7.02/1.42  --stats_out                             all
% 7.02/1.42  
% 7.02/1.42  ------ General Options
% 7.02/1.42  
% 7.02/1.42  --fof                                   false
% 7.02/1.42  --time_out_real                         305.
% 7.02/1.42  --time_out_virtual                      -1.
% 7.02/1.42  --symbol_type_check                     false
% 7.02/1.42  --clausify_out                          false
% 7.02/1.42  --sig_cnt_out                           false
% 7.02/1.42  --trig_cnt_out                          false
% 7.02/1.42  --trig_cnt_out_tolerance                1.
% 7.02/1.42  --trig_cnt_out_sk_spl                   false
% 7.02/1.42  --abstr_cl_out                          false
% 7.02/1.42  
% 7.02/1.42  ------ Global Options
% 7.02/1.42  
% 7.02/1.42  --schedule                              default
% 7.02/1.42  --add_important_lit                     false
% 7.02/1.42  --prop_solver_per_cl                    1000
% 7.02/1.42  --min_unsat_core                        false
% 7.02/1.42  --soft_assumptions                      false
% 7.02/1.42  --soft_lemma_size                       3
% 7.02/1.42  --prop_impl_unit_size                   0
% 7.02/1.42  --prop_impl_unit                        []
% 7.02/1.42  --share_sel_clauses                     true
% 7.02/1.42  --reset_solvers                         false
% 7.02/1.42  --bc_imp_inh                            [conj_cone]
% 7.02/1.42  --conj_cone_tolerance                   3.
% 7.02/1.42  --extra_neg_conj                        none
% 7.02/1.42  --large_theory_mode                     true
% 7.02/1.42  --prolific_symb_bound                   200
% 7.02/1.42  --lt_threshold                          2000
% 7.02/1.42  --clause_weak_htbl                      true
% 7.02/1.42  --gc_record_bc_elim                     false
% 7.02/1.42  
% 7.02/1.42  ------ Preprocessing Options
% 7.02/1.42  
% 7.02/1.42  --preprocessing_flag                    true
% 7.02/1.42  --time_out_prep_mult                    0.1
% 7.02/1.42  --splitting_mode                        input
% 7.02/1.42  --splitting_grd                         true
% 7.02/1.42  --splitting_cvd                         false
% 7.02/1.42  --splitting_cvd_svl                     false
% 7.02/1.42  --splitting_nvd                         32
% 7.02/1.42  --sub_typing                            true
% 7.02/1.42  --prep_gs_sim                           true
% 7.02/1.42  --prep_unflatten                        true
% 7.02/1.42  --prep_res_sim                          true
% 7.02/1.42  --prep_upred                            true
% 7.02/1.42  --prep_sem_filter                       exhaustive
% 7.02/1.42  --prep_sem_filter_out                   false
% 7.02/1.42  --pred_elim                             true
% 7.02/1.42  --res_sim_input                         true
% 7.02/1.42  --eq_ax_congr_red                       true
% 7.02/1.42  --pure_diseq_elim                       true
% 7.02/1.42  --brand_transform                       false
% 7.02/1.42  --non_eq_to_eq                          false
% 7.02/1.42  --prep_def_merge                        true
% 7.02/1.42  --prep_def_merge_prop_impl              false
% 7.02/1.42  --prep_def_merge_mbd                    true
% 7.02/1.42  --prep_def_merge_tr_red                 false
% 7.02/1.42  --prep_def_merge_tr_cl                  false
% 7.02/1.42  --smt_preprocessing                     true
% 7.02/1.42  --smt_ac_axioms                         fast
% 7.02/1.42  --preprocessed_out                      false
% 7.02/1.42  --preprocessed_stats                    false
% 7.02/1.42  
% 7.02/1.42  ------ Abstraction refinement Options
% 7.02/1.42  
% 7.02/1.42  --abstr_ref                             []
% 7.02/1.42  --abstr_ref_prep                        false
% 7.02/1.42  --abstr_ref_until_sat                   false
% 7.02/1.42  --abstr_ref_sig_restrict                funpre
% 7.02/1.42  --abstr_ref_af_restrict_to_split_sk     false
% 7.02/1.42  --abstr_ref_under                       []
% 7.02/1.42  
% 7.02/1.42  ------ SAT Options
% 7.02/1.42  
% 7.02/1.42  --sat_mode                              false
% 7.02/1.42  --sat_fm_restart_options                ""
% 7.02/1.42  --sat_gr_def                            false
% 7.02/1.42  --sat_epr_types                         true
% 7.02/1.42  --sat_non_cyclic_types                  false
% 7.02/1.42  --sat_finite_models                     false
% 7.02/1.42  --sat_fm_lemmas                         false
% 7.02/1.42  --sat_fm_prep                           false
% 7.02/1.42  --sat_fm_uc_incr                        true
% 7.02/1.42  --sat_out_model                         small
% 7.02/1.42  --sat_out_clauses                       false
% 7.02/1.42  
% 7.02/1.42  ------ QBF Options
% 7.02/1.42  
% 7.02/1.42  --qbf_mode                              false
% 7.02/1.42  --qbf_elim_univ                         false
% 7.02/1.42  --qbf_dom_inst                          none
% 7.02/1.42  --qbf_dom_pre_inst                      false
% 7.02/1.42  --qbf_sk_in                             false
% 7.02/1.42  --qbf_pred_elim                         true
% 7.02/1.42  --qbf_split                             512
% 7.02/1.42  
% 7.02/1.42  ------ BMC1 Options
% 7.02/1.42  
% 7.02/1.42  --bmc1_incremental                      false
% 7.02/1.42  --bmc1_axioms                           reachable_all
% 7.02/1.42  --bmc1_min_bound                        0
% 7.02/1.42  --bmc1_max_bound                        -1
% 7.02/1.42  --bmc1_max_bound_default                -1
% 7.02/1.42  --bmc1_symbol_reachability              true
% 7.02/1.42  --bmc1_property_lemmas                  false
% 7.02/1.42  --bmc1_k_induction                      false
% 7.02/1.42  --bmc1_non_equiv_states                 false
% 7.02/1.42  --bmc1_deadlock                         false
% 7.02/1.42  --bmc1_ucm                              false
% 7.02/1.42  --bmc1_add_unsat_core                   none
% 7.02/1.42  --bmc1_unsat_core_children              false
% 7.02/1.42  --bmc1_unsat_core_extrapolate_axioms    false
% 7.02/1.42  --bmc1_out_stat                         full
% 7.02/1.42  --bmc1_ground_init                      false
% 7.02/1.42  --bmc1_pre_inst_next_state              false
% 7.02/1.42  --bmc1_pre_inst_state                   false
% 7.02/1.42  --bmc1_pre_inst_reach_state             false
% 7.02/1.42  --bmc1_out_unsat_core                   false
% 7.02/1.42  --bmc1_aig_witness_out                  false
% 7.02/1.42  --bmc1_verbose                          false
% 7.02/1.42  --bmc1_dump_clauses_tptp                false
% 7.02/1.42  --bmc1_dump_unsat_core_tptp             false
% 7.02/1.42  --bmc1_dump_file                        -
% 7.02/1.42  --bmc1_ucm_expand_uc_limit              128
% 7.02/1.42  --bmc1_ucm_n_expand_iterations          6
% 7.02/1.42  --bmc1_ucm_extend_mode                  1
% 7.02/1.42  --bmc1_ucm_init_mode                    2
% 7.02/1.42  --bmc1_ucm_cone_mode                    none
% 7.02/1.42  --bmc1_ucm_reduced_relation_type        0
% 7.02/1.42  --bmc1_ucm_relax_model                  4
% 7.02/1.42  --bmc1_ucm_full_tr_after_sat            true
% 7.02/1.42  --bmc1_ucm_expand_neg_assumptions       false
% 7.02/1.42  --bmc1_ucm_layered_model                none
% 7.02/1.42  --bmc1_ucm_max_lemma_size               10
% 7.02/1.42  
% 7.02/1.42  ------ AIG Options
% 7.02/1.42  
% 7.02/1.42  --aig_mode                              false
% 7.02/1.42  
% 7.02/1.42  ------ Instantiation Options
% 7.02/1.42  
% 7.02/1.42  --instantiation_flag                    true
% 7.02/1.42  --inst_sos_flag                         false
% 7.02/1.42  --inst_sos_phase                        true
% 7.02/1.42  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.02/1.42  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.02/1.42  --inst_lit_sel_side                     none
% 7.02/1.42  --inst_solver_per_active                1400
% 7.02/1.42  --inst_solver_calls_frac                1.
% 7.02/1.42  --inst_passive_queue_type               priority_queues
% 7.02/1.42  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.02/1.42  --inst_passive_queues_freq              [25;2]
% 7.02/1.42  --inst_dismatching                      true
% 7.02/1.42  --inst_eager_unprocessed_to_passive     true
% 7.02/1.42  --inst_prop_sim_given                   true
% 7.02/1.42  --inst_prop_sim_new                     false
% 7.02/1.42  --inst_subs_new                         false
% 7.02/1.42  --inst_eq_res_simp                      false
% 7.02/1.42  --inst_subs_given                       false
% 7.02/1.42  --inst_orphan_elimination               true
% 7.02/1.42  --inst_learning_loop_flag               true
% 7.02/1.42  --inst_learning_start                   3000
% 7.02/1.42  --inst_learning_factor                  2
% 7.02/1.42  --inst_start_prop_sim_after_learn       3
% 7.02/1.42  --inst_sel_renew                        solver
% 7.02/1.42  --inst_lit_activity_flag                true
% 7.02/1.42  --inst_restr_to_given                   false
% 7.02/1.42  --inst_activity_threshold               500
% 7.02/1.42  --inst_out_proof                        true
% 7.02/1.42  
% 7.02/1.42  ------ Resolution Options
% 7.02/1.42  
% 7.02/1.42  --resolution_flag                       false
% 7.02/1.42  --res_lit_sel                           adaptive
% 7.02/1.42  --res_lit_sel_side                      none
% 7.02/1.42  --res_ordering                          kbo
% 7.02/1.42  --res_to_prop_solver                    active
% 7.02/1.42  --res_prop_simpl_new                    false
% 7.02/1.42  --res_prop_simpl_given                  true
% 7.02/1.42  --res_passive_queue_type                priority_queues
% 7.02/1.42  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.02/1.42  --res_passive_queues_freq               [15;5]
% 7.02/1.42  --res_forward_subs                      full
% 7.02/1.42  --res_backward_subs                     full
% 7.02/1.42  --res_forward_subs_resolution           true
% 7.02/1.42  --res_backward_subs_resolution          true
% 7.02/1.42  --res_orphan_elimination                true
% 7.02/1.42  --res_time_limit                        2.
% 7.02/1.42  --res_out_proof                         true
% 7.02/1.42  
% 7.02/1.42  ------ Superposition Options
% 7.02/1.42  
% 7.02/1.42  --superposition_flag                    true
% 7.02/1.42  --sup_passive_queue_type                priority_queues
% 7.02/1.42  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.02/1.42  --sup_passive_queues_freq               [8;1;4]
% 7.02/1.42  --demod_completeness_check              fast
% 7.02/1.42  --demod_use_ground                      true
% 7.02/1.42  --sup_to_prop_solver                    passive
% 7.02/1.42  --sup_prop_simpl_new                    true
% 7.02/1.42  --sup_prop_simpl_given                  true
% 7.02/1.42  --sup_fun_splitting                     false
% 7.02/1.42  --sup_smt_interval                      50000
% 7.02/1.42  
% 7.02/1.42  ------ Superposition Simplification Setup
% 7.02/1.42  
% 7.02/1.42  --sup_indices_passive                   []
% 7.02/1.42  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.02/1.42  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.02/1.42  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.02/1.42  --sup_full_triv                         [TrivRules;PropSubs]
% 7.02/1.42  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.02/1.42  --sup_full_bw                           [BwDemod]
% 7.02/1.42  --sup_immed_triv                        [TrivRules]
% 7.02/1.42  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.02/1.42  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.02/1.42  --sup_immed_bw_main                     []
% 7.02/1.42  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.02/1.42  --sup_input_triv                        [Unflattening;TrivRules]
% 7.02/1.42  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.02/1.42  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.02/1.42  
% 7.02/1.42  ------ Combination Options
% 7.02/1.42  
% 7.02/1.42  --comb_res_mult                         3
% 7.02/1.42  --comb_sup_mult                         2
% 7.02/1.42  --comb_inst_mult                        10
% 7.02/1.42  
% 7.02/1.42  ------ Debug Options
% 7.02/1.42  
% 7.02/1.42  --dbg_backtrace                         false
% 7.02/1.42  --dbg_dump_prop_clauses                 false
% 7.02/1.42  --dbg_dump_prop_clauses_file            -
% 7.02/1.42  --dbg_out_stat                          false
% 7.02/1.42  
% 7.02/1.42  
% 7.02/1.42  
% 7.02/1.42  
% 7.02/1.42  ------ Proving...
% 7.02/1.42  
% 7.02/1.42  
% 7.02/1.42  % SZS status Theorem for theBenchmark.p
% 7.02/1.42  
% 7.02/1.42  % SZS output start CNFRefutation for theBenchmark.p
% 7.02/1.42  
% 7.02/1.42  fof(f5,axiom,(
% 7.02/1.42    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 7.02/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.02/1.42  
% 7.02/1.42  fof(f24,plain,(
% 7.02/1.42    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 7.02/1.42    inference(ennf_transformation,[],[f5])).
% 7.02/1.42  
% 7.02/1.42  fof(f25,plain,(
% 7.02/1.42    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 7.02/1.42    inference(flattening,[],[f24])).
% 7.02/1.42  
% 7.02/1.42  fof(f52,plain,(
% 7.02/1.42    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 7.02/1.42    inference(nnf_transformation,[],[f25])).
% 7.02/1.42  
% 7.02/1.42  fof(f53,plain,(
% 7.02/1.42    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 7.02/1.42    inference(rectify,[],[f52])).
% 7.02/1.42  
% 7.02/1.42  fof(f55,plain,(
% 7.02/1.42    ( ! [X1] : (! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (k1_lattices(X0,k2_lattices(X0,X1,sK5(X0)),sK5(X0)) != sK5(X0) & m1_subset_1(sK5(X0),u1_struct_0(X0))))) )),
% 7.02/1.42    introduced(choice_axiom,[])).
% 7.02/1.42  
% 7.02/1.42  fof(f54,plain,(
% 7.02/1.42    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK4(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 7.02/1.42    introduced(choice_axiom,[])).
% 7.02/1.42  
% 7.02/1.42  fof(f56,plain,(
% 7.02/1.42    ! [X0] : (((v8_lattices(X0) | ((k1_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),sK5(X0)) != sK5(X0) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 7.02/1.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f53,f55,f54])).
% 7.02/1.42  
% 7.02/1.42  fof(f78,plain,(
% 7.02/1.42    ( ! [X4,X0,X3] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v8_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 7.02/1.42    inference(cnf_transformation,[],[f56])).
% 7.02/1.42  
% 7.02/1.42  fof(f13,conjecture,(
% 7.02/1.42    ! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1)))),
% 7.02/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.02/1.42  
% 7.02/1.42  fof(f14,negated_conjecture,(
% 7.02/1.42    ~! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1)))),
% 7.02/1.42    inference(negated_conjecture,[],[f13])).
% 7.02/1.42  
% 7.02/1.42  fof(f39,plain,(
% 7.02/1.42    ? [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 7.02/1.42    inference(ennf_transformation,[],[f14])).
% 7.02/1.42  
% 7.02/1.42  fof(f40,plain,(
% 7.02/1.42    ? [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 7.02/1.42    inference(flattening,[],[f39])).
% 7.02/1.42  
% 7.02/1.42  fof(f59,plain,(
% 7.02/1.42    ( ! [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) => (k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),sK7) & m1_subset_1(sK7,u1_struct_0(X0)))) )),
% 7.02/1.42    introduced(choice_axiom,[])).
% 7.02/1.42  
% 7.02/1.42  fof(f58,plain,(
% 7.02/1.42    ? [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (k5_lattices(sK6) != k4_lattices(sK6,k5_lattices(sK6),X1) & m1_subset_1(X1,u1_struct_0(sK6))) & l3_lattices(sK6) & v13_lattices(sK6) & v10_lattices(sK6) & ~v2_struct_0(sK6))),
% 7.02/1.42    introduced(choice_axiom,[])).
% 7.02/1.42  
% 7.02/1.42  fof(f60,plain,(
% 7.02/1.42    (k5_lattices(sK6) != k4_lattices(sK6,k5_lattices(sK6),sK7) & m1_subset_1(sK7,u1_struct_0(sK6))) & l3_lattices(sK6) & v13_lattices(sK6) & v10_lattices(sK6) & ~v2_struct_0(sK6)),
% 7.02/1.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f40,f59,f58])).
% 7.02/1.42  
% 7.02/1.42  fof(f94,plain,(
% 7.02/1.42    l3_lattices(sK6)),
% 7.02/1.42    inference(cnf_transformation,[],[f60])).
% 7.02/1.42  
% 7.02/1.42  fof(f91,plain,(
% 7.02/1.42    ~v2_struct_0(sK6)),
% 7.02/1.42    inference(cnf_transformation,[],[f60])).
% 7.02/1.42  
% 7.02/1.42  fof(f92,plain,(
% 7.02/1.42    v10_lattices(sK6)),
% 7.02/1.42    inference(cnf_transformation,[],[f60])).
% 7.02/1.42  
% 7.02/1.42  fof(f1,axiom,(
% 7.02/1.42    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 7.02/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.02/1.42  
% 7.02/1.42  fof(f15,plain,(
% 7.02/1.42    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 7.02/1.42    inference(pure_predicate_removal,[],[f1])).
% 7.02/1.42  
% 7.02/1.42  fof(f16,plain,(
% 7.02/1.42    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 7.02/1.42    inference(ennf_transformation,[],[f15])).
% 7.02/1.42  
% 7.02/1.42  fof(f17,plain,(
% 7.02/1.42    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 7.02/1.42    inference(flattening,[],[f16])).
% 7.02/1.42  
% 7.02/1.42  fof(f65,plain,(
% 7.02/1.42    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 7.02/1.42    inference(cnf_transformation,[],[f17])).
% 7.02/1.42  
% 7.02/1.42  fof(f3,axiom,(
% 7.02/1.42    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 7.02/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.02/1.42  
% 7.02/1.42  fof(f20,plain,(
% 7.02/1.42    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 7.02/1.42    inference(ennf_transformation,[],[f3])).
% 7.02/1.42  
% 7.02/1.42  fof(f21,plain,(
% 7.02/1.42    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 7.02/1.42    inference(flattening,[],[f20])).
% 7.02/1.42  
% 7.02/1.42  fof(f45,plain,(
% 7.02/1.42    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 7.02/1.42    inference(nnf_transformation,[],[f21])).
% 7.02/1.42  
% 7.02/1.42  fof(f72,plain,(
% 7.02/1.42    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 7.02/1.42    inference(cnf_transformation,[],[f45])).
% 7.02/1.42  
% 7.02/1.42  fof(f8,axiom,(
% 7.02/1.42    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 7.02/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.02/1.42  
% 7.02/1.42  fof(f30,plain,(
% 7.02/1.42    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 7.02/1.42    inference(ennf_transformation,[],[f8])).
% 7.02/1.42  
% 7.02/1.42  fof(f85,plain,(
% 7.02/1.42    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 7.02/1.42    inference(cnf_transformation,[],[f30])).
% 7.02/1.42  
% 7.02/1.42  fof(f2,axiom,(
% 7.02/1.42    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 7.02/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.02/1.42  
% 7.02/1.42  fof(f18,plain,(
% 7.02/1.42    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 7.02/1.42    inference(ennf_transformation,[],[f2])).
% 7.02/1.42  
% 7.02/1.42  fof(f19,plain,(
% 7.02/1.42    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.02/1.42    inference(flattening,[],[f18])).
% 7.02/1.42  
% 7.02/1.42  fof(f41,plain,(
% 7.02/1.42    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.02/1.42    inference(nnf_transformation,[],[f19])).
% 7.02/1.42  
% 7.02/1.42  fof(f42,plain,(
% 7.02/1.42    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.02/1.42    inference(rectify,[],[f41])).
% 7.02/1.42  
% 7.02/1.42  fof(f43,plain,(
% 7.02/1.42    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK0(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0))))),
% 7.02/1.42    introduced(choice_axiom,[])).
% 7.02/1.42  
% 7.02/1.42  fof(f44,plain,(
% 7.02/1.42    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK0(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK0(X0,X1)) != X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.02/1.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 7.02/1.42  
% 7.02/1.42  fof(f67,plain,(
% 7.02/1.42    ( ! [X0,X3,X1] : (k2_lattices(X0,X1,X3) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 7.02/1.42    inference(cnf_transformation,[],[f44])).
% 7.02/1.42  
% 7.02/1.42  fof(f98,plain,(
% 7.02/1.42    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 7.02/1.42    inference(equality_resolution,[],[f67])).
% 7.02/1.42  
% 7.02/1.42  fof(f93,plain,(
% 7.02/1.42    v13_lattices(sK6)),
% 7.02/1.42    inference(cnf_transformation,[],[f60])).
% 7.02/1.42  
% 7.02/1.42  fof(f84,plain,(
% 7.02/1.42    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 7.02/1.42    inference(cnf_transformation,[],[f30])).
% 7.02/1.42  
% 7.02/1.42  fof(f7,axiom,(
% 7.02/1.42    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 7.02/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.02/1.42  
% 7.02/1.42  fof(f28,plain,(
% 7.02/1.42    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 7.02/1.42    inference(ennf_transformation,[],[f7])).
% 7.02/1.42  
% 7.02/1.42  fof(f29,plain,(
% 7.02/1.42    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 7.02/1.42    inference(flattening,[],[f28])).
% 7.02/1.42  
% 7.02/1.42  fof(f83,plain,(
% 7.02/1.42    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 7.02/1.42    inference(cnf_transformation,[],[f29])).
% 7.02/1.42  
% 7.02/1.42  fof(f11,axiom,(
% 7.02/1.42    ! [X0] : ((l3_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,k4_lattices(X0,X1,X2),X1))))),
% 7.02/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.02/1.42  
% 7.02/1.42  fof(f35,plain,(
% 7.02/1.42    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 7.02/1.42    inference(ennf_transformation,[],[f11])).
% 7.02/1.42  
% 7.02/1.42  fof(f36,plain,(
% 7.02/1.42    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 7.02/1.42    inference(flattening,[],[f35])).
% 7.02/1.42  
% 7.02/1.42  fof(f89,plain,(
% 7.02/1.42    ( ! [X2,X0,X1] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 7.02/1.42    inference(cnf_transformation,[],[f36])).
% 7.02/1.42  
% 7.02/1.42  fof(f64,plain,(
% 7.02/1.42    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 7.02/1.42    inference(cnf_transformation,[],[f17])).
% 7.02/1.42  
% 7.02/1.42  fof(f6,axiom,(
% 7.02/1.42    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 7.02/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.02/1.42  
% 7.02/1.42  fof(f26,plain,(
% 7.02/1.42    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 7.02/1.42    inference(ennf_transformation,[],[f6])).
% 7.02/1.42  
% 7.02/1.42  fof(f27,plain,(
% 7.02/1.42    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 7.02/1.42    inference(flattening,[],[f26])).
% 7.02/1.42  
% 7.02/1.42  fof(f82,plain,(
% 7.02/1.42    ( ! [X2,X0,X1] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 7.02/1.42    inference(cnf_transformation,[],[f27])).
% 7.02/1.42  
% 7.02/1.42  fof(f62,plain,(
% 7.02/1.42    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 7.02/1.42    inference(cnf_transformation,[],[f17])).
% 7.02/1.42  
% 7.02/1.42  fof(f12,axiom,(
% 7.02/1.42    ! [X0] : ((l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_lattices(X0,X2,X1) & r1_lattices(X0,X1,X2)) => X1 = X2))))),
% 7.02/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.02/1.42  
% 7.02/1.42  fof(f37,plain,(
% 7.02/1.42    ! [X0] : (! [X1] : (! [X2] : ((X1 = X2 | (~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 7.02/1.42    inference(ennf_transformation,[],[f12])).
% 7.02/1.42  
% 7.02/1.42  fof(f38,plain,(
% 7.02/1.42    ! [X0] : (! [X1] : (! [X2] : (X1 = X2 | ~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 7.02/1.42    inference(flattening,[],[f37])).
% 7.02/1.42  
% 7.02/1.42  fof(f90,plain,(
% 7.02/1.42    ( ! [X2,X0,X1] : (X1 = X2 | ~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 7.02/1.42    inference(cnf_transformation,[],[f38])).
% 7.02/1.42  
% 7.02/1.42  fof(f96,plain,(
% 7.02/1.42    k5_lattices(sK6) != k4_lattices(sK6,k5_lattices(sK6),sK7)),
% 7.02/1.42    inference(cnf_transformation,[],[f60])).
% 7.02/1.42  
% 7.02/1.42  fof(f95,plain,(
% 7.02/1.42    m1_subset_1(sK7,u1_struct_0(sK6))),
% 7.02/1.42    inference(cnf_transformation,[],[f60])).
% 7.02/1.42  
% 7.02/1.42  cnf(c_1071,plain,
% 7.02/1.42      ( X0_55 != X1_55 | X2_55 != X1_55 | X2_55 = X0_55 ),
% 7.02/1.42      theory(equality) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_2504,plain,
% 7.02/1.42      ( X0_55 != X1_55
% 7.02/1.42      | X0_55 = k2_lattices(sK6,X2_55,X3_55)
% 7.02/1.42      | k2_lattices(sK6,X2_55,X3_55) != X1_55 ),
% 7.02/1.42      inference(instantiation,[status(thm)],[c_1071]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_3987,plain,
% 7.02/1.42      ( X0_55 = k2_lattices(sK6,k5_lattices(sK6),X1_55)
% 7.02/1.42      | X0_55 != k5_lattices(sK6)
% 7.02/1.42      | k2_lattices(sK6,k5_lattices(sK6),X1_55) != k5_lattices(sK6) ),
% 7.02/1.42      inference(instantiation,[status(thm)],[c_2504]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_7906,plain,
% 7.02/1.42      ( k2_lattices(sK6,k5_lattices(sK6),X0_55) != k5_lattices(sK6)
% 7.02/1.42      | k5_lattices(sK6) = k2_lattices(sK6,k5_lattices(sK6),X0_55)
% 7.02/1.42      | k5_lattices(sK6) != k5_lattices(sK6) ),
% 7.02/1.42      inference(instantiation,[status(thm)],[c_3987]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_16922,plain,
% 7.02/1.42      ( k2_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),sK7)) != k5_lattices(sK6)
% 7.02/1.42      | k5_lattices(sK6) = k2_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),sK7))
% 7.02/1.42      | k5_lattices(sK6) != k5_lattices(sK6) ),
% 7.02/1.42      inference(instantiation,[status(thm)],[c_7906]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_1074,plain,
% 7.02/1.42      ( ~ r1_lattices(X0_57,X0_55,X1_55)
% 7.02/1.42      | r1_lattices(X0_57,X2_55,X1_55)
% 7.02/1.42      | X2_55 != X0_55 ),
% 7.02/1.42      theory(equality) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_2391,plain,
% 7.02/1.42      ( ~ r1_lattices(sK6,X0_55,k4_lattices(sK6,k5_lattices(sK6),X1_55))
% 7.02/1.42      | r1_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),X1_55))
% 7.02/1.42      | k5_lattices(sK6) != X0_55 ),
% 7.02/1.42      inference(instantiation,[status(thm)],[c_1074]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_5240,plain,
% 7.02/1.42      ( ~ r1_lattices(sK6,k2_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),sK7)),k4_lattices(sK6,k5_lattices(sK6),sK7))
% 7.02/1.42      | r1_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),sK7))
% 7.02/1.42      | k5_lattices(sK6) != k2_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),sK7)) ),
% 7.02/1.42      inference(instantiation,[status(thm)],[c_2391]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_20,plain,
% 7.02/1.42      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.02/1.42      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.02/1.42      | ~ v8_lattices(X1)
% 7.02/1.42      | ~ l3_lattices(X1)
% 7.02/1.42      | v2_struct_0(X1)
% 7.02/1.42      | k1_lattices(X1,k2_lattices(X1,X0,X2),X2) = X2 ),
% 7.02/1.42      inference(cnf_transformation,[],[f78]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_32,negated_conjecture,
% 7.02/1.42      ( l3_lattices(sK6) ),
% 7.02/1.42      inference(cnf_transformation,[],[f94]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_834,plain,
% 7.02/1.42      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.02/1.42      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.02/1.42      | ~ v8_lattices(X1)
% 7.02/1.42      | v2_struct_0(X1)
% 7.02/1.42      | k1_lattices(X1,k2_lattices(X1,X0,X2),X2) = X2
% 7.02/1.42      | sK6 != X1 ),
% 7.02/1.42      inference(resolution_lifted,[status(thm)],[c_20,c_32]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_835,plain,
% 7.02/1.42      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.02/1.42      | ~ v8_lattices(sK6)
% 7.02/1.42      | v2_struct_0(sK6)
% 7.02/1.42      | k1_lattices(sK6,k2_lattices(sK6,X1,X0),X0) = X0 ),
% 7.02/1.42      inference(unflattening,[status(thm)],[c_834]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_35,negated_conjecture,
% 7.02/1.42      ( ~ v2_struct_0(sK6) ),
% 7.02/1.42      inference(cnf_transformation,[],[f91]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_34,negated_conjecture,
% 7.02/1.42      ( v10_lattices(sK6) ),
% 7.02/1.42      inference(cnf_transformation,[],[f92]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_1,plain,
% 7.02/1.42      ( v8_lattices(X0)
% 7.02/1.42      | ~ l3_lattices(X0)
% 7.02/1.42      | v2_struct_0(X0)
% 7.02/1.42      | ~ v10_lattices(X0) ),
% 7.02/1.42      inference(cnf_transformation,[],[f65]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_124,plain,
% 7.02/1.42      ( v8_lattices(sK6)
% 7.02/1.42      | ~ l3_lattices(sK6)
% 7.02/1.42      | v2_struct_0(sK6)
% 7.02/1.42      | ~ v10_lattices(sK6) ),
% 7.02/1.42      inference(instantiation,[status(thm)],[c_1]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_839,plain,
% 7.02/1.42      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.02/1.42      | k1_lattices(sK6,k2_lattices(sK6,X1,X0),X0) = X0 ),
% 7.02/1.42      inference(global_propositional_subsumption,
% 7.02/1.42                [status(thm)],
% 7.02/1.42                [c_835,c_35,c_34,c_32,c_124]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_840,plain,
% 7.02/1.42      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.02/1.42      | k1_lattices(sK6,k2_lattices(sK6,X0,X1),X1) = X1 ),
% 7.02/1.42      inference(renaming,[status(thm)],[c_839]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_1054,plain,
% 7.02/1.42      ( ~ m1_subset_1(X0_55,u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(X1_55,u1_struct_0(sK6))
% 7.02/1.42      | k1_lattices(sK6,k2_lattices(sK6,X0_55,X1_55),X1_55) = X1_55 ),
% 7.02/1.42      inference(subtyping,[status(esa)],[c_840]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_1684,plain,
% 7.02/1.42      ( ~ m1_subset_1(X0_55,u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(k4_lattices(sK6,k5_lattices(sK6),sK7),u1_struct_0(sK6))
% 7.02/1.42      | k1_lattices(sK6,k2_lattices(sK6,X0_55,k4_lattices(sK6,k5_lattices(sK6),sK7)),k4_lattices(sK6,k5_lattices(sK6),sK7)) = k4_lattices(sK6,k5_lattices(sK6),sK7) ),
% 7.02/1.42      inference(instantiation,[status(thm)],[c_1054]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_2955,plain,
% 7.02/1.42      ( ~ m1_subset_1(k4_lattices(sK6,k5_lattices(sK6),sK7),u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6))
% 7.02/1.42      | k1_lattices(sK6,k2_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),sK7)),k4_lattices(sK6,k5_lattices(sK6),sK7)) = k4_lattices(sK6,k5_lattices(sK6),sK7) ),
% 7.02/1.42      inference(instantiation,[status(thm)],[c_1684]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_10,plain,
% 7.02/1.42      ( r1_lattices(X0,X1,X2)
% 7.02/1.42      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.02/1.42      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.02/1.42      | ~ l2_lattices(X0)
% 7.02/1.42      | v2_struct_0(X0)
% 7.02/1.42      | k1_lattices(X0,X1,X2) != X2 ),
% 7.02/1.42      inference(cnf_transformation,[],[f72]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_895,plain,
% 7.02/1.42      ( r1_lattices(X0,X1,X2)
% 7.02/1.42      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.02/1.42      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.02/1.42      | ~ l2_lattices(X0)
% 7.02/1.42      | k1_lattices(X0,X1,X2) != X2
% 7.02/1.42      | sK6 != X0 ),
% 7.02/1.42      inference(resolution_lifted,[status(thm)],[c_10,c_35]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_896,plain,
% 7.02/1.42      ( r1_lattices(sK6,X0,X1)
% 7.02/1.42      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.02/1.42      | ~ l2_lattices(sK6)
% 7.02/1.42      | k1_lattices(sK6,X0,X1) != X1 ),
% 7.02/1.42      inference(unflattening,[status(thm)],[c_895]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_23,plain,
% 7.02/1.42      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 7.02/1.42      inference(cnf_transformation,[],[f85]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_60,plain,
% 7.02/1.42      ( l2_lattices(sK6) | ~ l3_lattices(sK6) ),
% 7.02/1.42      inference(instantiation,[status(thm)],[c_23]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_898,plain,
% 7.02/1.42      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.02/1.42      | r1_lattices(sK6,X0,X1)
% 7.02/1.42      | k1_lattices(sK6,X0,X1) != X1 ),
% 7.02/1.42      inference(global_propositional_subsumption,
% 7.02/1.42                [status(thm)],
% 7.02/1.42                [c_896,c_32,c_60]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_899,plain,
% 7.02/1.42      ( r1_lattices(sK6,X0,X1)
% 7.02/1.42      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.02/1.42      | k1_lattices(sK6,X0,X1) != X1 ),
% 7.02/1.42      inference(renaming,[status(thm)],[c_898]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_1052,plain,
% 7.02/1.42      ( r1_lattices(sK6,X0_55,X1_55)
% 7.02/1.42      | ~ m1_subset_1(X0_55,u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(X1_55,u1_struct_0(sK6))
% 7.02/1.42      | k1_lattices(sK6,X0_55,X1_55) != X1_55 ),
% 7.02/1.42      inference(subtyping,[status(esa)],[c_899]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_1601,plain,
% 7.02/1.42      ( r1_lattices(sK6,X0_55,k4_lattices(sK6,k5_lattices(sK6),sK7))
% 7.02/1.42      | ~ m1_subset_1(X0_55,u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(k4_lattices(sK6,k5_lattices(sK6),sK7),u1_struct_0(sK6))
% 7.02/1.42      | k1_lattices(sK6,X0_55,k4_lattices(sK6,k5_lattices(sK6),sK7)) != k4_lattices(sK6,k5_lattices(sK6),sK7) ),
% 7.02/1.42      inference(instantiation,[status(thm)],[c_1052]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_1683,plain,
% 7.02/1.42      ( r1_lattices(sK6,k2_lattices(sK6,X0_55,k4_lattices(sK6,k5_lattices(sK6),sK7)),k4_lattices(sK6,k5_lattices(sK6),sK7))
% 7.02/1.42      | ~ m1_subset_1(k4_lattices(sK6,k5_lattices(sK6),sK7),u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(k2_lattices(sK6,X0_55,k4_lattices(sK6,k5_lattices(sK6),sK7)),u1_struct_0(sK6))
% 7.02/1.42      | k1_lattices(sK6,k2_lattices(sK6,X0_55,k4_lattices(sK6,k5_lattices(sK6),sK7)),k4_lattices(sK6,k5_lattices(sK6),sK7)) != k4_lattices(sK6,k5_lattices(sK6),sK7) ),
% 7.02/1.42      inference(instantiation,[status(thm)],[c_1601]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_2594,plain,
% 7.02/1.42      ( r1_lattices(sK6,k2_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),sK7)),k4_lattices(sK6,k5_lattices(sK6),sK7))
% 7.02/1.42      | ~ m1_subset_1(k4_lattices(sK6,k5_lattices(sK6),sK7),u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(k2_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),sK7)),u1_struct_0(sK6))
% 7.02/1.42      | k1_lattices(sK6,k2_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),sK7)),k4_lattices(sK6,k5_lattices(sK6),sK7)) != k4_lattices(sK6,k5_lattices(sK6),sK7) ),
% 7.02/1.42      inference(instantiation,[status(thm)],[c_1683]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_9,plain,
% 7.02/1.42      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.02/1.42      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
% 7.02/1.42      | ~ l1_lattices(X1)
% 7.02/1.42      | ~ v13_lattices(X1)
% 7.02/1.42      | v2_struct_0(X1)
% 7.02/1.42      | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1) ),
% 7.02/1.42      inference(cnf_transformation,[],[f98]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_33,negated_conjecture,
% 7.02/1.42      ( v13_lattices(sK6) ),
% 7.02/1.42      inference(cnf_transformation,[],[f93]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_514,plain,
% 7.02/1.42      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.02/1.42      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
% 7.02/1.42      | ~ l1_lattices(X1)
% 7.02/1.42      | v2_struct_0(X1)
% 7.02/1.42      | k2_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1)
% 7.02/1.42      | sK6 != X1 ),
% 7.02/1.42      inference(resolution_lifted,[status(thm)],[c_9,c_33]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_515,plain,
% 7.02/1.42      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6))
% 7.02/1.42      | ~ l1_lattices(sK6)
% 7.02/1.42      | v2_struct_0(sK6)
% 7.02/1.42      | k2_lattices(sK6,k5_lattices(sK6),X0) = k5_lattices(sK6) ),
% 7.02/1.42      inference(unflattening,[status(thm)],[c_514]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_24,plain,
% 7.02/1.42      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 7.02/1.42      inference(cnf_transformation,[],[f84]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_57,plain,
% 7.02/1.42      ( l1_lattices(sK6) | ~ l3_lattices(sK6) ),
% 7.02/1.42      inference(instantiation,[status(thm)],[c_24]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_22,plain,
% 7.02/1.42      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 7.02/1.42      | ~ l1_lattices(X0)
% 7.02/1.42      | v2_struct_0(X0) ),
% 7.02/1.42      inference(cnf_transformation,[],[f83]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_63,plain,
% 7.02/1.42      ( m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6))
% 7.02/1.42      | ~ l1_lattices(sK6)
% 7.02/1.42      | v2_struct_0(sK6) ),
% 7.02/1.42      inference(instantiation,[status(thm)],[c_22]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_519,plain,
% 7.02/1.42      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.02/1.42      | k2_lattices(sK6,k5_lattices(sK6),X0) = k5_lattices(sK6) ),
% 7.02/1.42      inference(global_propositional_subsumption,
% 7.02/1.42                [status(thm)],
% 7.02/1.42                [c_515,c_35,c_32,c_57,c_63]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_1062,plain,
% 7.02/1.42      ( ~ m1_subset_1(X0_55,u1_struct_0(sK6))
% 7.02/1.42      | k2_lattices(sK6,k5_lattices(sK6),X0_55) = k5_lattices(sK6) ),
% 7.02/1.42      inference(subtyping,[status(esa)],[c_519]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_2267,plain,
% 7.02/1.42      ( ~ m1_subset_1(k4_lattices(sK6,k5_lattices(sK6),sK7),u1_struct_0(sK6))
% 7.02/1.42      | k2_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),sK7)) = k5_lattices(sK6) ),
% 7.02/1.42      inference(instantiation,[status(thm)],[c_1062]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_1073,plain,
% 7.02/1.42      ( ~ m1_subset_1(X0_55,X0_56)
% 7.02/1.42      | m1_subset_1(X1_55,X0_56)
% 7.02/1.42      | X1_55 != X0_55 ),
% 7.02/1.42      theory(equality) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_1521,plain,
% 7.02/1.42      ( m1_subset_1(X0_55,u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6))
% 7.02/1.42      | X0_55 != k5_lattices(sK6) ),
% 7.02/1.42      inference(instantiation,[status(thm)],[c_1073]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_1834,plain,
% 7.02/1.42      ( m1_subset_1(k2_lattices(sK6,X0_55,k4_lattices(sK6,k5_lattices(sK6),sK7)),u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6))
% 7.02/1.42      | k2_lattices(sK6,X0_55,k4_lattices(sK6,k5_lattices(sK6),sK7)) != k5_lattices(sK6) ),
% 7.02/1.42      inference(instantiation,[status(thm)],[c_1521]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_2266,plain,
% 7.02/1.42      ( m1_subset_1(k2_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),sK7)),u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6))
% 7.02/1.42      | k2_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),sK7)) != k5_lattices(sK6) ),
% 7.02/1.42      inference(instantiation,[status(thm)],[c_1834]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_1070,plain,( X0_55 = X0_55 ),theory(equality) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_1756,plain,
% 7.02/1.42      ( k5_lattices(sK6) = k5_lattices(sK6) ),
% 7.02/1.42      inference(instantiation,[status(thm)],[c_1070]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_28,plain,
% 7.02/1.42      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
% 7.02/1.42      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.02/1.42      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.02/1.42      | ~ v6_lattices(X0)
% 7.02/1.42      | ~ v8_lattices(X0)
% 7.02/1.42      | ~ l3_lattices(X0)
% 7.02/1.42      | v2_struct_0(X0) ),
% 7.02/1.42      inference(cnf_transformation,[],[f89]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_2,plain,
% 7.02/1.42      ( v6_lattices(X0)
% 7.02/1.42      | ~ l3_lattices(X0)
% 7.02/1.42      | v2_struct_0(X0)
% 7.02/1.42      | ~ v10_lattices(X0) ),
% 7.02/1.42      inference(cnf_transformation,[],[f64]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_467,plain,
% 7.02/1.42      ( v6_lattices(X0)
% 7.02/1.42      | ~ l3_lattices(X0)
% 7.02/1.42      | v2_struct_0(X0)
% 7.02/1.42      | sK6 != X0 ),
% 7.02/1.42      inference(resolution_lifted,[status(thm)],[c_2,c_34]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_468,plain,
% 7.02/1.42      ( v6_lattices(sK6) | ~ l3_lattices(sK6) | v2_struct_0(sK6) ),
% 7.02/1.42      inference(unflattening,[status(thm)],[c_467]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_121,plain,
% 7.02/1.42      ( v6_lattices(sK6)
% 7.02/1.42      | ~ l3_lattices(sK6)
% 7.02/1.42      | v2_struct_0(sK6)
% 7.02/1.42      | ~ v10_lattices(sK6) ),
% 7.02/1.42      inference(instantiation,[status(thm)],[c_2]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_470,plain,
% 7.02/1.42      ( v6_lattices(sK6) ),
% 7.02/1.42      inference(global_propositional_subsumption,
% 7.02/1.42                [status(thm)],
% 7.02/1.42                [c_468,c_35,c_34,c_32,c_121]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_740,plain,
% 7.02/1.42      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
% 7.02/1.42      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.02/1.42      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.02/1.42      | ~ v8_lattices(X0)
% 7.02/1.42      | ~ l3_lattices(X0)
% 7.02/1.42      | v2_struct_0(X0)
% 7.02/1.42      | sK6 != X0 ),
% 7.02/1.42      inference(resolution_lifted,[status(thm)],[c_28,c_470]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_741,plain,
% 7.02/1.42      ( r1_lattices(sK6,k4_lattices(sK6,X0,X1),X0)
% 7.02/1.42      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.02/1.42      | ~ v8_lattices(sK6)
% 7.02/1.42      | ~ l3_lattices(sK6)
% 7.02/1.42      | v2_struct_0(sK6) ),
% 7.02/1.42      inference(unflattening,[status(thm)],[c_740]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_745,plain,
% 7.02/1.42      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.02/1.42      | r1_lattices(sK6,k4_lattices(sK6,X0,X1),X0) ),
% 7.02/1.42      inference(global_propositional_subsumption,
% 7.02/1.42                [status(thm)],
% 7.02/1.42                [c_741,c_35,c_34,c_32,c_124]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_746,plain,
% 7.02/1.42      ( r1_lattices(sK6,k4_lattices(sK6,X0,X1),X0)
% 7.02/1.42      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 7.02/1.42      inference(renaming,[status(thm)],[c_745]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_1058,plain,
% 7.02/1.42      ( r1_lattices(sK6,k4_lattices(sK6,X0_55,X1_55),X0_55)
% 7.02/1.42      | ~ m1_subset_1(X0_55,u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(X1_55,u1_struct_0(sK6)) ),
% 7.02/1.42      inference(subtyping,[status(esa)],[c_746]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_1589,plain,
% 7.02/1.42      ( r1_lattices(sK6,k4_lattices(sK6,k5_lattices(sK6),sK7),k5_lattices(sK6))
% 7.02/1.42      | ~ m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
% 7.02/1.42      inference(instantiation,[status(thm)],[c_1058]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_21,plain,
% 7.02/1.42      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.02/1.42      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.02/1.42      | m1_subset_1(k4_lattices(X1,X0,X2),u1_struct_0(X1))
% 7.02/1.42      | ~ l1_lattices(X1)
% 7.02/1.42      | ~ v6_lattices(X1)
% 7.02/1.42      | v2_struct_0(X1) ),
% 7.02/1.42      inference(cnf_transformation,[],[f82]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_624,plain,
% 7.02/1.42      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.02/1.42      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.02/1.42      | m1_subset_1(k4_lattices(X1,X0,X2),u1_struct_0(X1))
% 7.02/1.42      | ~ v6_lattices(X1)
% 7.02/1.42      | ~ l3_lattices(X3)
% 7.02/1.42      | v2_struct_0(X1)
% 7.02/1.42      | X1 != X3 ),
% 7.02/1.42      inference(resolution_lifted,[status(thm)],[c_24,c_21]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_625,plain,
% 7.02/1.42      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.02/1.42      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.02/1.42      | m1_subset_1(k4_lattices(X1,X0,X2),u1_struct_0(X1))
% 7.02/1.42      | ~ v6_lattices(X1)
% 7.02/1.42      | ~ l3_lattices(X1)
% 7.02/1.42      | v2_struct_0(X1) ),
% 7.02/1.42      inference(unflattening,[status(thm)],[c_624]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_761,plain,
% 7.02/1.42      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.02/1.42      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.02/1.42      | m1_subset_1(k4_lattices(X1,X0,X2),u1_struct_0(X1))
% 7.02/1.42      | ~ l3_lattices(X1)
% 7.02/1.42      | v2_struct_0(X1)
% 7.02/1.42      | sK6 != X1 ),
% 7.02/1.42      inference(resolution_lifted,[status(thm)],[c_625,c_470]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_762,plain,
% 7.02/1.42      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.02/1.42      | m1_subset_1(k4_lattices(sK6,X1,X0),u1_struct_0(sK6))
% 7.02/1.42      | ~ l3_lattices(sK6)
% 7.02/1.42      | v2_struct_0(sK6) ),
% 7.02/1.42      inference(unflattening,[status(thm)],[c_761]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_766,plain,
% 7.02/1.42      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.02/1.42      | m1_subset_1(k4_lattices(sK6,X1,X0),u1_struct_0(sK6)) ),
% 7.02/1.42      inference(global_propositional_subsumption,
% 7.02/1.42                [status(thm)],
% 7.02/1.42                [c_762,c_35,c_32]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_767,plain,
% 7.02/1.42      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.02/1.42      | m1_subset_1(k4_lattices(sK6,X0,X1),u1_struct_0(sK6)) ),
% 7.02/1.42      inference(renaming,[status(thm)],[c_766]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_1057,plain,
% 7.02/1.42      ( ~ m1_subset_1(X0_55,u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(X1_55,u1_struct_0(sK6))
% 7.02/1.42      | m1_subset_1(k4_lattices(sK6,X0_55,X1_55),u1_struct_0(sK6)) ),
% 7.02/1.42      inference(subtyping,[status(esa)],[c_767]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_1541,plain,
% 7.02/1.42      ( m1_subset_1(k4_lattices(sK6,k5_lattices(sK6),sK7),u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
% 7.02/1.42      inference(instantiation,[status(thm)],[c_1057]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_4,plain,
% 7.02/1.42      ( v4_lattices(X0)
% 7.02/1.42      | ~ l3_lattices(X0)
% 7.02/1.42      | v2_struct_0(X0)
% 7.02/1.42      | ~ v10_lattices(X0) ),
% 7.02/1.42      inference(cnf_transformation,[],[f62]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_29,plain,
% 7.02/1.42      ( ~ r1_lattices(X0,X1,X2)
% 7.02/1.42      | ~ r1_lattices(X0,X2,X1)
% 7.02/1.42      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.02/1.42      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.02/1.42      | ~ l2_lattices(X0)
% 7.02/1.42      | ~ v4_lattices(X0)
% 7.02/1.42      | v2_struct_0(X0)
% 7.02/1.42      | X2 = X1 ),
% 7.02/1.42      inference(cnf_transformation,[],[f90]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_385,plain,
% 7.02/1.42      ( ~ r1_lattices(X0,X1,X2)
% 7.02/1.42      | ~ r1_lattices(X0,X2,X1)
% 7.02/1.42      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.02/1.42      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.02/1.42      | ~ l2_lattices(X0)
% 7.02/1.42      | ~ l3_lattices(X0)
% 7.02/1.42      | v2_struct_0(X0)
% 7.02/1.42      | ~ v10_lattices(X0)
% 7.02/1.42      | X2 = X1 ),
% 7.02/1.42      inference(resolution,[status(thm)],[c_4,c_29]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_389,plain,
% 7.02/1.42      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.02/1.42      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.02/1.42      | ~ r1_lattices(X0,X2,X1)
% 7.02/1.42      | ~ r1_lattices(X0,X1,X2)
% 7.02/1.42      | ~ l3_lattices(X0)
% 7.02/1.42      | v2_struct_0(X0)
% 7.02/1.42      | ~ v10_lattices(X0)
% 7.02/1.42      | X2 = X1 ),
% 7.02/1.42      inference(global_propositional_subsumption,
% 7.02/1.42                [status(thm)],
% 7.02/1.42                [c_385,c_23]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_390,plain,
% 7.02/1.42      ( ~ r1_lattices(X0,X1,X2)
% 7.02/1.42      | ~ r1_lattices(X0,X2,X1)
% 7.02/1.42      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.02/1.42      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.02/1.42      | ~ l3_lattices(X0)
% 7.02/1.42      | v2_struct_0(X0)
% 7.02/1.42      | ~ v10_lattices(X0)
% 7.02/1.42      | X2 = X1 ),
% 7.02/1.42      inference(renaming,[status(thm)],[c_389]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_429,plain,
% 7.02/1.42      ( ~ r1_lattices(X0,X1,X2)
% 7.02/1.42      | ~ r1_lattices(X0,X2,X1)
% 7.02/1.42      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.02/1.42      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.02/1.42      | ~ l3_lattices(X0)
% 7.02/1.42      | v2_struct_0(X0)
% 7.02/1.42      | X2 = X1
% 7.02/1.42      | sK6 != X0 ),
% 7.02/1.42      inference(resolution_lifted,[status(thm)],[c_390,c_34]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_430,plain,
% 7.02/1.42      ( ~ r1_lattices(sK6,X0,X1)
% 7.02/1.42      | ~ r1_lattices(sK6,X1,X0)
% 7.02/1.42      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.02/1.42      | ~ l3_lattices(sK6)
% 7.02/1.42      | v2_struct_0(sK6)
% 7.02/1.42      | X0 = X1 ),
% 7.02/1.42      inference(unflattening,[status(thm)],[c_429]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_434,plain,
% 7.02/1.42      ( ~ r1_lattices(sK6,X0,X1)
% 7.02/1.42      | ~ r1_lattices(sK6,X1,X0)
% 7.02/1.42      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.02/1.42      | X0 = X1 ),
% 7.02/1.42      inference(global_propositional_subsumption,
% 7.02/1.42                [status(thm)],
% 7.02/1.42                [c_430,c_35,c_32]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_435,plain,
% 7.02/1.42      ( ~ r1_lattices(sK6,X0,X1)
% 7.02/1.42      | ~ r1_lattices(sK6,X1,X0)
% 7.02/1.42      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.02/1.42      | X0 = X1 ),
% 7.02/1.42      inference(renaming,[status(thm)],[c_434]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_1063,plain,
% 7.02/1.42      ( ~ r1_lattices(sK6,X0_55,X1_55)
% 7.02/1.42      | ~ r1_lattices(sK6,X1_55,X0_55)
% 7.02/1.42      | ~ m1_subset_1(X0_55,u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(X1_55,u1_struct_0(sK6))
% 7.02/1.42      | X0_55 = X1_55 ),
% 7.02/1.42      inference(subtyping,[status(esa)],[c_435]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_1513,plain,
% 7.02/1.42      ( ~ r1_lattices(sK6,k4_lattices(sK6,k5_lattices(sK6),sK7),k5_lattices(sK6))
% 7.02/1.42      | ~ r1_lattices(sK6,k5_lattices(sK6),k4_lattices(sK6,k5_lattices(sK6),sK7))
% 7.02/1.42      | ~ m1_subset_1(k4_lattices(sK6,k5_lattices(sK6),sK7),u1_struct_0(sK6))
% 7.02/1.42      | ~ m1_subset_1(k5_lattices(sK6),u1_struct_0(sK6))
% 7.02/1.42      | k5_lattices(sK6) = k4_lattices(sK6,k5_lattices(sK6),sK7) ),
% 7.02/1.42      inference(instantiation,[status(thm)],[c_1063]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_30,negated_conjecture,
% 7.02/1.42      ( k5_lattices(sK6) != k4_lattices(sK6,k5_lattices(sK6),sK7) ),
% 7.02/1.42      inference(cnf_transformation,[],[f96]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_1065,negated_conjecture,
% 7.02/1.42      ( k5_lattices(sK6) != k4_lattices(sK6,k5_lattices(sK6),sK7) ),
% 7.02/1.42      inference(subtyping,[status(esa)],[c_30]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(c_31,negated_conjecture,
% 7.02/1.42      ( m1_subset_1(sK7,u1_struct_0(sK6)) ),
% 7.02/1.42      inference(cnf_transformation,[],[f95]) ).
% 7.02/1.42  
% 7.02/1.42  cnf(contradiction,plain,
% 7.02/1.42      ( $false ),
% 7.02/1.42      inference(minisat,
% 7.02/1.42                [status(thm)],
% 7.02/1.42                [c_16922,c_5240,c_2955,c_2594,c_2267,c_2266,c_1756,
% 7.02/1.42                 c_1589,c_1541,c_1513,c_1065,c_63,c_57,c_31,c_32,c_35]) ).
% 7.02/1.42  
% 7.02/1.42  
% 7.02/1.42  % SZS output end CNFRefutation for theBenchmark.p
% 7.02/1.42  
% 7.02/1.42  ------                               Statistics
% 7.02/1.42  
% 7.02/1.42  ------ General
% 7.02/1.42  
% 7.02/1.42  abstr_ref_over_cycles:                  0
% 7.02/1.42  abstr_ref_under_cycles:                 0
% 7.02/1.42  gc_basic_clause_elim:                   0
% 7.02/1.42  forced_gc_time:                         0
% 7.02/1.42  parsing_time:                           0.008
% 7.02/1.42  unif_index_cands_time:                  0.
% 7.02/1.42  unif_index_add_time:                    0.
% 7.02/1.42  orderings_time:                         0.
% 7.02/1.42  out_proof_time:                         0.012
% 7.02/1.42  total_time:                             0.512
% 7.02/1.42  num_of_symbols:                         60
% 7.02/1.42  num_of_terms:                           16100
% 7.02/1.43  
% 7.02/1.43  ------ Preprocessing
% 7.02/1.43  
% 7.02/1.43  num_of_splits:                          2
% 7.02/1.43  num_of_split_atoms:                     2
% 7.02/1.43  num_of_reused_defs:                     0
% 7.02/1.43  num_eq_ax_congr_red:                    33
% 7.02/1.43  num_of_sem_filtered_clauses:            3
% 7.02/1.43  num_of_subtypes:                        3
% 7.02/1.43  monotx_restored_types:                  0
% 7.02/1.43  sat_num_of_epr_types:                   0
% 7.02/1.43  sat_num_of_non_cyclic_types:            0
% 7.02/1.43  sat_guarded_non_collapsed_types:        1
% 7.02/1.43  num_pure_diseq_elim:                    0
% 7.02/1.43  simp_replaced_by:                       0
% 7.02/1.43  res_preprocessed:                       97
% 7.02/1.43  prep_upred:                             0
% 7.02/1.43  prep_unflattend:                        30
% 7.02/1.43  smt_new_axioms:                         0
% 7.02/1.43  pred_elim_cands:                        2
% 7.02/1.43  pred_elim:                              12
% 7.02/1.43  pred_elim_cl:                           20
% 7.02/1.43  pred_elim_cycles:                       14
% 7.02/1.43  merged_defs:                            0
% 7.02/1.43  merged_defs_ncl:                        0
% 7.02/1.43  bin_hyper_res:                          0
% 7.02/1.43  prep_cycles:                            4
% 7.02/1.43  pred_elim_time:                         0.011
% 7.02/1.43  splitting_time:                         0.
% 7.02/1.43  sem_filter_time:                        0.
% 7.02/1.43  monotx_time:                            0.
% 7.02/1.43  subtype_inf_time:                       0.
% 7.02/1.43  
% 7.02/1.43  ------ Problem properties
% 7.02/1.43  
% 7.02/1.43  clauses:                                17
% 7.02/1.43  conjectures:                            2
% 7.02/1.43  epr:                                    1
% 7.02/1.43  horn:                                   15
% 7.02/1.43  ground:                                 4
% 7.02/1.43  unary:                                  3
% 7.02/1.43  binary:                                 4
% 7.02/1.43  lits:                                   47
% 7.02/1.43  lits_eq:                                12
% 7.02/1.43  fd_pure:                                0
% 7.02/1.43  fd_pseudo:                              0
% 7.02/1.43  fd_cond:                                2
% 7.02/1.43  fd_pseudo_cond:                         1
% 7.02/1.43  ac_symbols:                             0
% 7.02/1.43  
% 7.02/1.43  ------ Propositional Solver
% 7.02/1.43  
% 7.02/1.43  prop_solver_calls:                      33
% 7.02/1.43  prop_fast_solver_calls:                 1275
% 7.02/1.43  smt_solver_calls:                       0
% 7.02/1.43  smt_fast_solver_calls:                  0
% 7.02/1.43  prop_num_of_clauses:                    6482
% 7.02/1.43  prop_preprocess_simplified:             13060
% 7.02/1.43  prop_fo_subsumed:                       89
% 7.02/1.43  prop_solver_time:                       0.
% 7.02/1.43  smt_solver_time:                        0.
% 7.02/1.43  smt_fast_solver_time:                   0.
% 7.02/1.43  prop_fast_solver_time:                  0.
% 7.02/1.43  prop_unsat_core_time:                   0.001
% 7.02/1.43  
% 7.02/1.43  ------ QBF
% 7.02/1.43  
% 7.02/1.43  qbf_q_res:                              0
% 7.02/1.43  qbf_num_tautologies:                    0
% 7.02/1.43  qbf_prep_cycles:                        0
% 7.02/1.43  
% 7.02/1.43  ------ BMC1
% 7.02/1.43  
% 7.02/1.43  bmc1_current_bound:                     -1
% 7.02/1.43  bmc1_last_solved_bound:                 -1
% 7.02/1.43  bmc1_unsat_core_size:                   -1
% 7.02/1.43  bmc1_unsat_core_parents_size:           -1
% 7.02/1.43  bmc1_merge_next_fun:                    0
% 7.02/1.43  bmc1_unsat_core_clauses_time:           0.
% 7.02/1.43  
% 7.02/1.43  ------ Instantiation
% 7.02/1.43  
% 7.02/1.43  inst_num_of_clauses:                    2116
% 7.02/1.43  inst_num_in_passive:                    929
% 7.02/1.43  inst_num_in_active:                     835
% 7.02/1.43  inst_num_in_unprocessed:                351
% 7.02/1.43  inst_num_of_loops:                      921
% 7.02/1.43  inst_num_of_learning_restarts:          0
% 7.02/1.43  inst_num_moves_active_passive:          80
% 7.02/1.43  inst_lit_activity:                      0
% 7.02/1.43  inst_lit_activity_moves:                0
% 7.02/1.43  inst_num_tautologies:                   0
% 7.02/1.43  inst_num_prop_implied:                  0
% 7.02/1.43  inst_num_existing_simplified:           0
% 7.02/1.43  inst_num_eq_res_simplified:             0
% 7.02/1.43  inst_num_child_elim:                    0
% 7.02/1.43  inst_num_of_dismatching_blockings:      1698
% 7.02/1.43  inst_num_of_non_proper_insts:           3111
% 7.02/1.43  inst_num_of_duplicates:                 0
% 7.02/1.43  inst_inst_num_from_inst_to_res:         0
% 7.02/1.43  inst_dismatching_checking_time:         0.
% 7.02/1.43  
% 7.02/1.43  ------ Resolution
% 7.02/1.43  
% 7.02/1.43  res_num_of_clauses:                     0
% 7.02/1.43  res_num_in_passive:                     0
% 7.02/1.43  res_num_in_active:                      0
% 7.02/1.43  res_num_of_loops:                       101
% 7.02/1.43  res_forward_subset_subsumed:            202
% 7.02/1.43  res_backward_subset_subsumed:           0
% 7.02/1.43  res_forward_subsumed:                   0
% 7.02/1.43  res_backward_subsumed:                  0
% 7.02/1.43  res_forward_subsumption_resolution:     0
% 7.02/1.43  res_backward_subsumption_resolution:    0
% 7.02/1.43  res_clause_to_clause_subsumption:       2021
% 7.02/1.43  res_orphan_elimination:                 0
% 7.02/1.43  res_tautology_del:                      378
% 7.02/1.43  res_num_eq_res_simplified:              0
% 7.02/1.43  res_num_sel_changes:                    0
% 7.02/1.43  res_moves_from_active_to_pass:          0
% 7.02/1.43  
% 7.02/1.43  ------ Superposition
% 7.02/1.43  
% 7.02/1.43  sup_time_total:                         0.
% 7.02/1.43  sup_time_generating:                    0.
% 7.02/1.43  sup_time_sim_full:                      0.
% 7.02/1.43  sup_time_sim_immed:                     0.
% 7.02/1.43  
% 7.02/1.43  sup_num_of_clauses:                     344
% 7.02/1.43  sup_num_in_active:                      178
% 7.02/1.43  sup_num_in_passive:                     166
% 7.02/1.43  sup_num_of_loops:                       184
% 7.02/1.43  sup_fw_superposition:                   295
% 7.02/1.43  sup_bw_superposition:                   75
% 7.02/1.43  sup_immediate_simplified:               25
% 7.02/1.43  sup_given_eliminated:                   0
% 7.02/1.43  comparisons_done:                       0
% 7.02/1.43  comparisons_avoided:                    18
% 7.02/1.43  
% 7.02/1.43  ------ Simplifications
% 7.02/1.43  
% 7.02/1.43  
% 7.02/1.43  sim_fw_subset_subsumed:                 7
% 7.02/1.43  sim_bw_subset_subsumed:                 0
% 7.02/1.43  sim_fw_subsumed:                        3
% 7.02/1.43  sim_bw_subsumed:                        0
% 7.02/1.43  sim_fw_subsumption_res:                 1
% 7.02/1.43  sim_bw_subsumption_res:                 0
% 7.02/1.43  sim_tautology_del:                      0
% 7.02/1.43  sim_eq_tautology_del:                   28
% 7.02/1.43  sim_eq_res_simp:                        1
% 7.02/1.43  sim_fw_demodulated:                     0
% 7.02/1.43  sim_bw_demodulated:                     6
% 7.02/1.43  sim_light_normalised:                   18
% 7.02/1.43  sim_joinable_taut:                      0
% 7.02/1.43  sim_joinable_simp:                      0
% 7.02/1.43  sim_ac_normalised:                      0
% 7.02/1.43  sim_smt_subsumption:                    0
% 7.02/1.43  
%------------------------------------------------------------------------------
