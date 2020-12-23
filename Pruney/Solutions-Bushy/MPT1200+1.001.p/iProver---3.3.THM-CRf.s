%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1200+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:08 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 481 expanded)
%              Number of clauses        :   70 ( 115 expanded)
%              Number of leaves         :   16 ( 172 expanded)
%              Depth                    :   19
%              Number of atoms          :  576 (3572 expanded)
%              Number of equality atoms :  113 ( 118 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
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

fof(f8,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f7])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  & r1_lattices(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v7_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  & r1_lattices(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v7_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
          & r1_lattices(X0,X1,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,k2_lattices(X0,X1,sK8),k2_lattices(X0,X2,sK8))
        & r1_lattices(X0,X1,X2)
        & m1_subset_1(sK8,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
              & r1_lattices(X0,X1,X2)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,sK7,X3))
            & r1_lattices(X0,X1,sK7)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK7,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  & r1_lattices(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_lattices(X0,k2_lattices(X0,sK6,X3),k2_lattices(X0,X2,X3))
                & r1_lattices(X0,sK6,X2)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                    & r1_lattices(X0,X1,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(sK5,k2_lattices(sK5,X1,X3),k2_lattices(sK5,X2,X3))
                  & r1_lattices(sK5,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(sK5)) )
              & m1_subset_1(X2,u1_struct_0(sK5)) )
          & m1_subset_1(X1,u1_struct_0(sK5)) )
      & l3_lattices(sK5)
      & v9_lattices(sK5)
      & v8_lattices(sK5)
      & v7_lattices(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ~ r1_lattices(sK5,k2_lattices(sK5,sK6,sK8),k2_lattices(sK5,sK7,sK8))
    & r1_lattices(sK5,sK6,sK7)
    & m1_subset_1(sK8,u1_struct_0(sK5))
    & m1_subset_1(sK7,u1_struct_0(sK5))
    & m1_subset_1(sK6,u1_struct_0(sK5))
    & l3_lattices(sK5)
    & v9_lattices(sK5)
    & v8_lattices(sK5)
    & v7_lattices(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f21,f38,f37,f36,f35])).

fof(f63,plain,(
    m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    l3_lattices(sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f13,plain,(
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

fof(f14,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k1_lattices(X0,k2_lattices(X0,X1,sK4(X0)),sK4(X0)) != sK4(X0)
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0)) != sK4(X0)
            & m1_subset_1(sK4(X0),u1_struct_0(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f30,f32,f31])).

fof(f47,plain,(
    ! [X4,X0,X3] :
      ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    v8_lattices(sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( v7_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0] :
      ( ( v7_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v7_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ! [X3] :
                      ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v7_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v7_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v7_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f23])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,k2_lattices(X0,X2,sK2(X0))) != k2_lattices(X0,k2_lattices(X0,X1,X2),sK2(X0))
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( k2_lattices(X0,X1,k2_lattices(X0,sK1(X0),X3)) != k2_lattices(X0,k2_lattices(X0,X1,sK1(X0)),X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k2_lattices(X0,k2_lattices(X0,sK0(X0),X2),X3) != k2_lattices(X0,sK0(X0),k2_lattices(X0,X2,X3))
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v7_lattices(X0)
          | ( k2_lattices(X0,k2_lattices(X0,sK0(X0),sK1(X0)),sK2(X0)) != k2_lattices(X0,sK0(X0),k2_lattices(X0,sK1(X0),sK2(X0)))
            & m1_subset_1(sK2(X0),u1_struct_0(X0))
            & m1_subset_1(sK1(X0),u1_struct_0(X0))
            & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v7_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).

fof(f42,plain,(
    ! [X6,X4,X0,X5] :
      ( k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v7_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f57,plain,(
    v7_lattices(sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,(
    r1_lattices(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    v9_lattices(sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    ~ r1_lattices(sK5,k2_lattices(sK5,sK6,sK8),k2_lattices(sK5,sK7,sK8)) ),
    inference(cnf_transformation,[],[f39])).

fof(f53,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
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

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k1_lattices(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_736,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_910,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_736])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_735,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_911,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_735])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_491,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_492,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(k2_lattices(sK5,X0,X1),u1_struct_0(sK5))
    | ~ l1_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_21,negated_conjecture,
    ( l3_lattices(sK5) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_13,plain,
    ( ~ l3_lattices(X0)
    | l1_lattices(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_43,plain,
    ( ~ l3_lattices(sK5)
    | l1_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_496,plain,
    ( m1_subset_1(k2_lattices(sK5,X0,X1),u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_492,c_21,c_43])).

cnf(c_497,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(k2_lattices(sK5,X1,X0),u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_496])).

cnf(c_732,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK5))
    | m1_subset_1(k2_lattices(sK5,X1_49,X0_49),u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_497])).

cnf(c_914,plain,
    ( m1_subset_1(X0_49,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(k2_lattices(sK5,X1_49,X0_49),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_734,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_912,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_734])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v8_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_446,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_447,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ v8_lattices(sK5)
    | v2_struct_0(sK5)
    | k1_lattices(sK5,k2_lattices(sK5,X0,X1),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_23,negated_conjecture,
    ( v8_lattices(sK5) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_451,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k1_lattices(sK5,k2_lattices(sK5,X0,X1),X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_447,c_25,c_23])).

cnf(c_452,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k1_lattices(sK5,k2_lattices(sK5,X1,X0),X0) = X0 ),
    inference(renaming,[status(thm)],[c_451])).

cnf(c_733,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK5))
    | k1_lattices(sK5,k2_lattices(sK5,X1_49,X0_49),X0_49) = X0_49 ),
    inference(subtyping,[status(esa)],[c_452])).

cnf(c_913,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,X0_49,X1_49),X1_49) = X1_49
    | m1_subset_1(X1_49,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_733])).

cnf(c_1106,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK6,X0_49),X0_49) = X0_49
    | m1_subset_1(X0_49,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_912,c_913])).

cnf(c_1708,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK6,k2_lattices(sK5,X0_49,X1_49)),k2_lattices(sK5,X0_49,X1_49)) = k2_lattices(sK5,X0_49,X1_49)
    | m1_subset_1(X1_49,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_914,c_1106])).

cnf(c_11116,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK6,k2_lattices(sK5,sK7,X0_49)),k2_lattices(sK5,sK7,X0_49)) = k2_lattices(sK5,sK7,X0_49)
    | m1_subset_1(X0_49,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_911,c_1708])).

cnf(c_11936,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK6,k2_lattices(sK5,sK7,sK8)),k2_lattices(sK5,sK7,sK8)) = k2_lattices(sK5,sK7,sK8) ),
    inference(superposition,[status(thm)],[c_910,c_11116])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v7_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,k2_lattices(X1,X3,X2),X0) = k2_lattices(X1,X3,k2_lattices(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_512,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v7_lattices(X1)
    | k2_lattices(X1,X3,k2_lattices(X1,X2,X0)) = k2_lattices(X1,k2_lattices(X1,X3,X2),X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_25])).

cnf(c_513,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ l1_lattices(sK5)
    | ~ v7_lattices(sK5)
    | k2_lattices(sK5,X2,k2_lattices(sK5,X0,X1)) = k2_lattices(sK5,k2_lattices(sK5,X2,X0),X1) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_24,negated_conjecture,
    ( v7_lattices(sK5) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_517,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | k2_lattices(sK5,X2,k2_lattices(sK5,X0,X1)) = k2_lattices(sK5,k2_lattices(sK5,X2,X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_513,c_24,c_21,c_43])).

cnf(c_518,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | k2_lattices(sK5,X1,k2_lattices(sK5,X2,X0)) = k2_lattices(sK5,k2_lattices(sK5,X1,X2),X0) ),
    inference(renaming,[status(thm)],[c_517])).

cnf(c_731,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK5))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK5))
    | k2_lattices(sK5,X1_49,k2_lattices(sK5,X2_49,X0_49)) = k2_lattices(sK5,k2_lattices(sK5,X1_49,X2_49),X0_49) ),
    inference(subtyping,[status(esa)],[c_518])).

cnf(c_915,plain,
    ( k2_lattices(sK5,X0_49,k2_lattices(sK5,X1_49,X2_49)) = k2_lattices(sK5,k2_lattices(sK5,X0_49,X1_49),X2_49)
    | m1_subset_1(X2_49,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_2087,plain,
    ( k2_lattices(sK5,k2_lattices(sK5,sK6,X0_49),X1_49) = k2_lattices(sK5,sK6,k2_lattices(sK5,X0_49,X1_49))
    | m1_subset_1(X0_49,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_912,c_915])).

cnf(c_4588,plain,
    ( k2_lattices(sK5,sK6,k2_lattices(sK5,sK7,X0_49)) = k2_lattices(sK5,k2_lattices(sK5,sK6,sK7),X0_49)
    | m1_subset_1(X0_49,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_911,c_2087])).

cnf(c_17,negated_conjecture,
    ( r1_lattices(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_15,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v9_lattices(X0)
    | ~ l3_lattices(X0)
    | ~ v8_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_22,negated_conjecture,
    ( v9_lattices(sK5) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_327,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | ~ v8_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) = X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_328,plain,
    ( ~ r1_lattices(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | ~ v8_lattices(sK5)
    | v2_struct_0(sK5)
    | k2_lattices(sK5,X0,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_332,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r1_lattices(sK5,X0,X1)
    | k2_lattices(sK5,X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_328,c_25,c_23,c_21])).

cnf(c_333,plain,
    ( ~ r1_lattices(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k2_lattices(sK5,X0,X1) = X0 ),
    inference(renaming,[status(thm)],[c_332])).

cnf(c_625,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k2_lattices(sK5,X1,X0) = X1
    | sK7 != X0
    | sK6 != X1
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_333])).

cnf(c_626,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | k2_lattices(sK5,sK6,sK7) = sK6 ),
    inference(unflattening,[status(thm)],[c_625])).

cnf(c_628,plain,
    ( k2_lattices(sK5,sK6,sK7) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_626,c_20,c_19])).

cnf(c_725,plain,
    ( k2_lattices(sK5,sK6,sK7) = sK6 ),
    inference(subtyping,[status(esa)],[c_628])).

cnf(c_4591,plain,
    ( k2_lattices(sK5,sK6,k2_lattices(sK5,sK7,X0_49)) = k2_lattices(sK5,sK6,X0_49)
    | m1_subset_1(X0_49,u1_struct_0(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4588,c_725])).

cnf(c_4991,plain,
    ( k2_lattices(sK5,sK6,k2_lattices(sK5,sK7,sK8)) = k2_lattices(sK5,sK6,sK8) ),
    inference(superposition,[status(thm)],[c_910,c_4591])).

cnf(c_11942,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK6,sK8),k2_lattices(sK5,sK7,sK8)) = k2_lattices(sK5,sK7,sK8) ),
    inference(light_normalisation,[status(thm)],[c_11936,c_4991])).

cnf(c_968,plain,
    ( m1_subset_1(k2_lattices(sK5,sK6,sK8),u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_732])).

cnf(c_946,plain,
    ( m1_subset_1(k2_lattices(sK5,sK7,sK8),u1_struct_0(sK5))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_732])).

cnf(c_16,negated_conjecture,
    ( ~ r1_lattices(sK5,k2_lattices(sK5,sK6,sK8),k2_lattices(sK5,sK7,sK8)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_12,plain,
    ( ~ l3_lattices(X0)
    | l2_lattices(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_0,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l2_lattices(X0)
    | k1_lattices(X0,X1,X2) != X2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_290,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) != X2 ),
    inference(resolution,[status(thm)],[c_12,c_0])).

cnf(c_385,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_290,c_21])).

cnf(c_386,plain,
    ( r1_lattices(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | v2_struct_0(sK5)
    | k1_lattices(sK5,X0,X1) != X1 ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r1_lattices(sK5,X0,X1)
    | k1_lattices(sK5,X0,X1) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_386,c_25])).

cnf(c_391,plain,
    ( r1_lattices(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k1_lattices(sK5,X0,X1) != X1 ),
    inference(renaming,[status(thm)],[c_390])).

cnf(c_591,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k2_lattices(sK5,sK7,sK8) != X0
    | k2_lattices(sK5,sK6,sK8) != X1
    | k1_lattices(sK5,X1,X0) != X0
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_391])).

cnf(c_592,plain,
    ( ~ m1_subset_1(k2_lattices(sK5,sK7,sK8),u1_struct_0(sK5))
    | ~ m1_subset_1(k2_lattices(sK5,sK6,sK8),u1_struct_0(sK5))
    | k1_lattices(sK5,k2_lattices(sK5,sK6,sK8),k2_lattices(sK5,sK7,sK8)) != k2_lattices(sK5,sK7,sK8) ),
    inference(unflattening,[status(thm)],[c_591])).

cnf(c_728,plain,
    ( ~ m1_subset_1(k2_lattices(sK5,sK7,sK8),u1_struct_0(sK5))
    | ~ m1_subset_1(k2_lattices(sK5,sK6,sK8),u1_struct_0(sK5))
    | k1_lattices(sK5,k2_lattices(sK5,sK6,sK8),k2_lattices(sK5,sK7,sK8)) != k2_lattices(sK5,sK7,sK8) ),
    inference(subtyping,[status(esa)],[c_592])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11942,c_968,c_946,c_728,c_18,c_19,c_20])).


%------------------------------------------------------------------------------
