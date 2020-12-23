%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:13 EST 2020

% Result     : Theorem 4.03s
% Output     : CNFRefutation 4.03s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

cnf(c_911,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_736])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_735,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_912,plain,
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

cnf(c_915,plain,
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

cnf(c_913,plain,
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

cnf(c_914,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,X0_49,X1_49),X1_49) = X1_49
    | m1_subset_1(X1_49,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_733])).

cnf(c_1131,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK6,X0_49),X0_49) = X0_49
    | m1_subset_1(X0_49,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_913,c_914])).

cnf(c_1723,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK6,k2_lattices(sK5,X0_49,X1_49)),k2_lattices(sK5,X0_49,X1_49)) = k2_lattices(sK5,X0_49,X1_49)
    | m1_subset_1(X1_49,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_915,c_1131])).

cnf(c_10970,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK6,k2_lattices(sK5,sK7,X0_49)),k2_lattices(sK5,sK7,X0_49)) = k2_lattices(sK5,sK7,X0_49)
    | m1_subset_1(X0_49,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_912,c_1723])).

cnf(c_12385,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK6,k2_lattices(sK5,sK7,sK8)),k2_lattices(sK5,sK7,sK8)) = k2_lattices(sK5,sK7,sK8) ),
    inference(superposition,[status(thm)],[c_911,c_10970])).

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

cnf(c_916,plain,
    ( k2_lattices(sK5,X0_49,k2_lattices(sK5,X1_49,X2_49)) = k2_lattices(sK5,k2_lattices(sK5,X0_49,X1_49),X2_49)
    | m1_subset_1(X2_49,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_2068,plain,
    ( k2_lattices(sK5,k2_lattices(sK5,sK6,X0_49),X1_49) = k2_lattices(sK5,sK6,k2_lattices(sK5,X0_49,X1_49))
    | m1_subset_1(X0_49,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_913,c_916])).

cnf(c_5223,plain,
    ( k2_lattices(sK5,sK6,k2_lattices(sK5,sK7,X0_49)) = k2_lattices(sK5,k2_lattices(sK5,sK6,sK7),X0_49)
    | m1_subset_1(X0_49,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_912,c_2068])).

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

cnf(c_5240,plain,
    ( k2_lattices(sK5,sK6,k2_lattices(sK5,sK7,X0_49)) = k2_lattices(sK5,sK6,X0_49)
    | m1_subset_1(X0_49,u1_struct_0(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5223,c_725])).

cnf(c_5753,plain,
    ( k2_lattices(sK5,sK6,k2_lattices(sK5,sK7,sK8)) = k2_lattices(sK5,sK6,sK8) ),
    inference(superposition,[status(thm)],[c_911,c_5240])).

cnf(c_12402,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK6,sK8),k2_lattices(sK5,sK7,sK8)) = k2_lattices(sK5,sK7,sK8) ),
    inference(light_normalisation,[status(thm)],[c_12385,c_5753])).

cnf(c_1072,plain,
    ( m1_subset_1(k2_lattices(sK5,sK6,sK8),u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_732])).

cnf(c_1004,plain,
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
    inference(minisat,[status(thm)],[c_12402,c_1072,c_1004,c_728,c_18,c_19,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:41:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.03/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.03/0.98  
% 4.03/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.03/0.98  
% 4.03/0.98  ------  iProver source info
% 4.03/0.98  
% 4.03/0.98  git: date: 2020-06-30 10:37:57 +0100
% 4.03/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.03/0.98  git: non_committed_changes: false
% 4.03/0.98  git: last_make_outside_of_git: false
% 4.03/0.98  
% 4.03/0.98  ------ 
% 4.03/0.98  
% 4.03/0.98  ------ Input Options
% 4.03/0.98  
% 4.03/0.98  --out_options                           all
% 4.03/0.98  --tptp_safe_out                         true
% 4.03/0.98  --problem_path                          ""
% 4.03/0.98  --include_path                          ""
% 4.03/0.98  --clausifier                            res/vclausify_rel
% 4.03/0.98  --clausifier_options                    --mode clausify
% 4.03/0.98  --stdin                                 false
% 4.03/0.98  --stats_out                             all
% 4.03/0.98  
% 4.03/0.98  ------ General Options
% 4.03/0.98  
% 4.03/0.98  --fof                                   false
% 4.03/0.98  --time_out_real                         305.
% 4.03/0.98  --time_out_virtual                      -1.
% 4.03/0.98  --symbol_type_check                     false
% 4.03/0.98  --clausify_out                          false
% 4.03/0.98  --sig_cnt_out                           false
% 4.03/0.98  --trig_cnt_out                          false
% 4.03/0.98  --trig_cnt_out_tolerance                1.
% 4.03/0.98  --trig_cnt_out_sk_spl                   false
% 4.03/0.98  --abstr_cl_out                          false
% 4.03/0.98  
% 4.03/0.98  ------ Global Options
% 4.03/0.98  
% 4.03/0.98  --schedule                              default
% 4.03/0.98  --add_important_lit                     false
% 4.03/0.98  --prop_solver_per_cl                    1000
% 4.03/0.98  --min_unsat_core                        false
% 4.03/0.98  --soft_assumptions                      false
% 4.03/0.98  --soft_lemma_size                       3
% 4.03/0.98  --prop_impl_unit_size                   0
% 4.03/0.98  --prop_impl_unit                        []
% 4.03/0.98  --share_sel_clauses                     true
% 4.03/0.98  --reset_solvers                         false
% 4.03/0.98  --bc_imp_inh                            [conj_cone]
% 4.03/0.98  --conj_cone_tolerance                   3.
% 4.03/0.98  --extra_neg_conj                        none
% 4.03/0.98  --large_theory_mode                     true
% 4.03/0.98  --prolific_symb_bound                   200
% 4.03/0.98  --lt_threshold                          2000
% 4.03/0.98  --clause_weak_htbl                      true
% 4.03/0.98  --gc_record_bc_elim                     false
% 4.03/0.98  
% 4.03/0.98  ------ Preprocessing Options
% 4.03/0.98  
% 4.03/0.98  --preprocessing_flag                    true
% 4.03/0.98  --time_out_prep_mult                    0.1
% 4.03/0.98  --splitting_mode                        input
% 4.03/0.98  --splitting_grd                         true
% 4.03/0.98  --splitting_cvd                         false
% 4.03/0.98  --splitting_cvd_svl                     false
% 4.03/0.98  --splitting_nvd                         32
% 4.03/0.98  --sub_typing                            true
% 4.03/0.98  --prep_gs_sim                           true
% 4.03/0.98  --prep_unflatten                        true
% 4.03/0.98  --prep_res_sim                          true
% 4.03/0.98  --prep_upred                            true
% 4.03/0.98  --prep_sem_filter                       exhaustive
% 4.03/0.98  --prep_sem_filter_out                   false
% 4.03/0.98  --pred_elim                             true
% 4.03/0.98  --res_sim_input                         true
% 4.03/0.98  --eq_ax_congr_red                       true
% 4.03/0.98  --pure_diseq_elim                       true
% 4.03/0.98  --brand_transform                       false
% 4.03/0.98  --non_eq_to_eq                          false
% 4.03/0.98  --prep_def_merge                        true
% 4.03/0.98  --prep_def_merge_prop_impl              false
% 4.03/0.98  --prep_def_merge_mbd                    true
% 4.03/0.98  --prep_def_merge_tr_red                 false
% 4.03/0.98  --prep_def_merge_tr_cl                  false
% 4.03/0.98  --smt_preprocessing                     true
% 4.03/0.98  --smt_ac_axioms                         fast
% 4.03/0.98  --preprocessed_out                      false
% 4.03/0.98  --preprocessed_stats                    false
% 4.03/0.98  
% 4.03/0.98  ------ Abstraction refinement Options
% 4.03/0.98  
% 4.03/0.98  --abstr_ref                             []
% 4.03/0.98  --abstr_ref_prep                        false
% 4.03/0.98  --abstr_ref_until_sat                   false
% 4.03/0.98  --abstr_ref_sig_restrict                funpre
% 4.03/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.03/0.98  --abstr_ref_under                       []
% 4.03/0.98  
% 4.03/0.98  ------ SAT Options
% 4.03/0.98  
% 4.03/0.98  --sat_mode                              false
% 4.03/0.98  --sat_fm_restart_options                ""
% 4.03/0.98  --sat_gr_def                            false
% 4.03/0.98  --sat_epr_types                         true
% 4.03/0.98  --sat_non_cyclic_types                  false
% 4.03/0.98  --sat_finite_models                     false
% 4.03/0.98  --sat_fm_lemmas                         false
% 4.03/0.98  --sat_fm_prep                           false
% 4.03/0.98  --sat_fm_uc_incr                        true
% 4.03/0.98  --sat_out_model                         small
% 4.03/0.98  --sat_out_clauses                       false
% 4.03/0.98  
% 4.03/0.98  ------ QBF Options
% 4.03/0.98  
% 4.03/0.98  --qbf_mode                              false
% 4.03/0.98  --qbf_elim_univ                         false
% 4.03/0.98  --qbf_dom_inst                          none
% 4.03/0.98  --qbf_dom_pre_inst                      false
% 4.03/0.98  --qbf_sk_in                             false
% 4.03/0.98  --qbf_pred_elim                         true
% 4.03/0.98  --qbf_split                             512
% 4.03/0.98  
% 4.03/0.98  ------ BMC1 Options
% 4.03/0.98  
% 4.03/0.98  --bmc1_incremental                      false
% 4.03/0.98  --bmc1_axioms                           reachable_all
% 4.03/0.98  --bmc1_min_bound                        0
% 4.03/0.98  --bmc1_max_bound                        -1
% 4.03/0.98  --bmc1_max_bound_default                -1
% 4.03/0.98  --bmc1_symbol_reachability              true
% 4.03/0.98  --bmc1_property_lemmas                  false
% 4.03/0.98  --bmc1_k_induction                      false
% 4.03/0.98  --bmc1_non_equiv_states                 false
% 4.03/0.98  --bmc1_deadlock                         false
% 4.03/0.98  --bmc1_ucm                              false
% 4.03/0.98  --bmc1_add_unsat_core                   none
% 4.03/0.98  --bmc1_unsat_core_children              false
% 4.03/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.03/0.98  --bmc1_out_stat                         full
% 4.03/0.98  --bmc1_ground_init                      false
% 4.03/0.98  --bmc1_pre_inst_next_state              false
% 4.03/0.98  --bmc1_pre_inst_state                   false
% 4.03/0.98  --bmc1_pre_inst_reach_state             false
% 4.03/0.98  --bmc1_out_unsat_core                   false
% 4.03/0.98  --bmc1_aig_witness_out                  false
% 4.03/0.98  --bmc1_verbose                          false
% 4.03/0.98  --bmc1_dump_clauses_tptp                false
% 4.03/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.03/0.98  --bmc1_dump_file                        -
% 4.03/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.03/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.03/0.98  --bmc1_ucm_extend_mode                  1
% 4.03/0.98  --bmc1_ucm_init_mode                    2
% 4.03/0.98  --bmc1_ucm_cone_mode                    none
% 4.03/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.03/0.98  --bmc1_ucm_relax_model                  4
% 4.03/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.03/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.03/0.98  --bmc1_ucm_layered_model                none
% 4.03/0.98  --bmc1_ucm_max_lemma_size               10
% 4.03/0.98  
% 4.03/0.98  ------ AIG Options
% 4.03/0.98  
% 4.03/0.98  --aig_mode                              false
% 4.03/0.98  
% 4.03/0.98  ------ Instantiation Options
% 4.03/0.98  
% 4.03/0.98  --instantiation_flag                    true
% 4.03/0.98  --inst_sos_flag                         false
% 4.03/0.98  --inst_sos_phase                        true
% 4.03/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.03/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.03/0.98  --inst_lit_sel_side                     num_symb
% 4.03/0.98  --inst_solver_per_active                1400
% 4.03/0.98  --inst_solver_calls_frac                1.
% 4.03/0.98  --inst_passive_queue_type               priority_queues
% 4.03/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.03/0.98  --inst_passive_queues_freq              [25;2]
% 4.03/0.98  --inst_dismatching                      true
% 4.03/0.98  --inst_eager_unprocessed_to_passive     true
% 4.03/0.98  --inst_prop_sim_given                   true
% 4.03/0.98  --inst_prop_sim_new                     false
% 4.03/0.98  --inst_subs_new                         false
% 4.03/0.98  --inst_eq_res_simp                      false
% 4.03/0.98  --inst_subs_given                       false
% 4.03/0.98  --inst_orphan_elimination               true
% 4.03/0.98  --inst_learning_loop_flag               true
% 4.03/0.98  --inst_learning_start                   3000
% 4.03/0.98  --inst_learning_factor                  2
% 4.03/0.98  --inst_start_prop_sim_after_learn       3
% 4.03/0.98  --inst_sel_renew                        solver
% 4.03/0.98  --inst_lit_activity_flag                true
% 4.03/0.98  --inst_restr_to_given                   false
% 4.03/0.98  --inst_activity_threshold               500
% 4.03/0.98  --inst_out_proof                        true
% 4.03/0.98  
% 4.03/0.98  ------ Resolution Options
% 4.03/0.98  
% 4.03/0.98  --resolution_flag                       true
% 4.03/0.98  --res_lit_sel                           adaptive
% 4.03/0.98  --res_lit_sel_side                      none
% 4.03/0.98  --res_ordering                          kbo
% 4.03/0.98  --res_to_prop_solver                    active
% 4.03/0.98  --res_prop_simpl_new                    false
% 4.03/0.98  --res_prop_simpl_given                  true
% 4.03/0.98  --res_passive_queue_type                priority_queues
% 4.03/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.03/0.98  --res_passive_queues_freq               [15;5]
% 4.03/0.98  --res_forward_subs                      full
% 4.03/0.98  --res_backward_subs                     full
% 4.03/0.98  --res_forward_subs_resolution           true
% 4.03/0.98  --res_backward_subs_resolution          true
% 4.03/0.98  --res_orphan_elimination                true
% 4.03/0.98  --res_time_limit                        2.
% 4.03/0.98  --res_out_proof                         true
% 4.03/0.98  
% 4.03/0.98  ------ Superposition Options
% 4.03/0.98  
% 4.03/0.98  --superposition_flag                    true
% 4.03/0.98  --sup_passive_queue_type                priority_queues
% 4.03/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.03/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.03/0.98  --demod_completeness_check              fast
% 4.03/0.98  --demod_use_ground                      true
% 4.03/0.98  --sup_to_prop_solver                    passive
% 4.03/0.98  --sup_prop_simpl_new                    true
% 4.03/0.98  --sup_prop_simpl_given                  true
% 4.03/0.98  --sup_fun_splitting                     false
% 4.03/0.98  --sup_smt_interval                      50000
% 4.03/0.98  
% 4.03/0.98  ------ Superposition Simplification Setup
% 4.03/0.98  
% 4.03/0.98  --sup_indices_passive                   []
% 4.03/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.03/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.03/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.03/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.03/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.03/0.98  --sup_full_bw                           [BwDemod]
% 4.03/0.98  --sup_immed_triv                        [TrivRules]
% 4.03/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.03/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.03/0.98  --sup_immed_bw_main                     []
% 4.03/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.03/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.03/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.03/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.03/0.98  
% 4.03/0.98  ------ Combination Options
% 4.03/0.98  
% 4.03/0.98  --comb_res_mult                         3
% 4.03/0.98  --comb_sup_mult                         2
% 4.03/0.98  --comb_inst_mult                        10
% 4.03/0.98  
% 4.03/0.98  ------ Debug Options
% 4.03/0.98  
% 4.03/0.98  --dbg_backtrace                         false
% 4.03/0.98  --dbg_dump_prop_clauses                 false
% 4.03/0.98  --dbg_dump_prop_clauses_file            -
% 4.03/0.98  --dbg_out_stat                          false
% 4.03/0.98  ------ Parsing...
% 4.03/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.03/0.98  
% 4.03/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 4.03/0.98  
% 4.03/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.03/0.98  
% 4.03/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.03/0.98  ------ Proving...
% 4.03/0.98  ------ Problem Properties 
% 4.03/0.98  
% 4.03/0.98  
% 4.03/0.98  clauses                                 13
% 4.03/0.98  conjectures                             3
% 4.03/0.98  EPR                                     0
% 4.03/0.98  Horn                                    13
% 4.03/0.98  unary                                   5
% 4.03/0.98  binary                                  1
% 4.03/0.98  lits                                    31
% 4.03/0.98  lits eq                                 12
% 4.03/0.98  fd_pure                                 0
% 4.03/0.98  fd_pseudo                               0
% 4.03/0.98  fd_cond                                 0
% 4.03/0.98  fd_pseudo_cond                          0
% 4.03/0.98  AC symbols                              0
% 4.03/0.98  
% 4.03/0.98  ------ Schedule dynamic 5 is on 
% 4.03/0.98  
% 4.03/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.03/0.98  
% 4.03/0.98  
% 4.03/0.98  ------ 
% 4.03/0.98  Current options:
% 4.03/0.98  ------ 
% 4.03/0.98  
% 4.03/0.98  ------ Input Options
% 4.03/0.98  
% 4.03/0.98  --out_options                           all
% 4.03/0.98  --tptp_safe_out                         true
% 4.03/0.98  --problem_path                          ""
% 4.03/0.98  --include_path                          ""
% 4.03/0.98  --clausifier                            res/vclausify_rel
% 4.03/0.98  --clausifier_options                    --mode clausify
% 4.03/0.98  --stdin                                 false
% 4.03/0.98  --stats_out                             all
% 4.03/0.98  
% 4.03/0.98  ------ General Options
% 4.03/0.98  
% 4.03/0.98  --fof                                   false
% 4.03/0.98  --time_out_real                         305.
% 4.03/0.98  --time_out_virtual                      -1.
% 4.03/0.98  --symbol_type_check                     false
% 4.03/0.98  --clausify_out                          false
% 4.03/0.98  --sig_cnt_out                           false
% 4.03/0.98  --trig_cnt_out                          false
% 4.03/0.98  --trig_cnt_out_tolerance                1.
% 4.03/0.98  --trig_cnt_out_sk_spl                   false
% 4.03/0.98  --abstr_cl_out                          false
% 4.03/0.98  
% 4.03/0.98  ------ Global Options
% 4.03/0.98  
% 4.03/0.98  --schedule                              default
% 4.03/0.98  --add_important_lit                     false
% 4.03/0.98  --prop_solver_per_cl                    1000
% 4.03/0.98  --min_unsat_core                        false
% 4.03/0.98  --soft_assumptions                      false
% 4.03/0.98  --soft_lemma_size                       3
% 4.03/0.98  --prop_impl_unit_size                   0
% 4.03/0.98  --prop_impl_unit                        []
% 4.03/0.98  --share_sel_clauses                     true
% 4.03/0.98  --reset_solvers                         false
% 4.03/0.98  --bc_imp_inh                            [conj_cone]
% 4.03/0.98  --conj_cone_tolerance                   3.
% 4.03/0.98  --extra_neg_conj                        none
% 4.03/0.98  --large_theory_mode                     true
% 4.03/0.98  --prolific_symb_bound                   200
% 4.03/0.98  --lt_threshold                          2000
% 4.03/0.98  --clause_weak_htbl                      true
% 4.03/0.98  --gc_record_bc_elim                     false
% 4.03/0.98  
% 4.03/0.98  ------ Preprocessing Options
% 4.03/0.98  
% 4.03/0.98  --preprocessing_flag                    true
% 4.03/0.98  --time_out_prep_mult                    0.1
% 4.03/0.98  --splitting_mode                        input
% 4.03/0.98  --splitting_grd                         true
% 4.03/0.98  --splitting_cvd                         false
% 4.03/0.98  --splitting_cvd_svl                     false
% 4.03/0.98  --splitting_nvd                         32
% 4.03/0.98  --sub_typing                            true
% 4.03/0.98  --prep_gs_sim                           true
% 4.03/0.98  --prep_unflatten                        true
% 4.03/0.98  --prep_res_sim                          true
% 4.03/0.98  --prep_upred                            true
% 4.03/0.98  --prep_sem_filter                       exhaustive
% 4.03/0.98  --prep_sem_filter_out                   false
% 4.03/0.98  --pred_elim                             true
% 4.03/0.98  --res_sim_input                         true
% 4.03/0.98  --eq_ax_congr_red                       true
% 4.03/0.98  --pure_diseq_elim                       true
% 4.03/0.98  --brand_transform                       false
% 4.03/0.98  --non_eq_to_eq                          false
% 4.03/0.98  --prep_def_merge                        true
% 4.03/0.98  --prep_def_merge_prop_impl              false
% 4.03/0.98  --prep_def_merge_mbd                    true
% 4.03/0.98  --prep_def_merge_tr_red                 false
% 4.03/0.98  --prep_def_merge_tr_cl                  false
% 4.03/0.98  --smt_preprocessing                     true
% 4.03/0.98  --smt_ac_axioms                         fast
% 4.03/0.98  --preprocessed_out                      false
% 4.03/0.98  --preprocessed_stats                    false
% 4.03/0.98  
% 4.03/0.98  ------ Abstraction refinement Options
% 4.03/0.98  
% 4.03/0.98  --abstr_ref                             []
% 4.03/0.98  --abstr_ref_prep                        false
% 4.03/0.98  --abstr_ref_until_sat                   false
% 4.03/0.98  --abstr_ref_sig_restrict                funpre
% 4.03/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.03/0.98  --abstr_ref_under                       []
% 4.03/0.98  
% 4.03/0.98  ------ SAT Options
% 4.03/0.98  
% 4.03/0.98  --sat_mode                              false
% 4.03/0.98  --sat_fm_restart_options                ""
% 4.03/0.98  --sat_gr_def                            false
% 4.03/0.98  --sat_epr_types                         true
% 4.03/0.98  --sat_non_cyclic_types                  false
% 4.03/0.98  --sat_finite_models                     false
% 4.03/0.98  --sat_fm_lemmas                         false
% 4.03/0.98  --sat_fm_prep                           false
% 4.03/0.98  --sat_fm_uc_incr                        true
% 4.03/0.98  --sat_out_model                         small
% 4.03/0.98  --sat_out_clauses                       false
% 4.03/0.98  
% 4.03/0.98  ------ QBF Options
% 4.03/0.98  
% 4.03/0.98  --qbf_mode                              false
% 4.03/0.98  --qbf_elim_univ                         false
% 4.03/0.98  --qbf_dom_inst                          none
% 4.03/0.98  --qbf_dom_pre_inst                      false
% 4.03/0.98  --qbf_sk_in                             false
% 4.03/0.98  --qbf_pred_elim                         true
% 4.03/0.98  --qbf_split                             512
% 4.03/0.98  
% 4.03/0.98  ------ BMC1 Options
% 4.03/0.98  
% 4.03/0.98  --bmc1_incremental                      false
% 4.03/0.98  --bmc1_axioms                           reachable_all
% 4.03/0.98  --bmc1_min_bound                        0
% 4.03/0.98  --bmc1_max_bound                        -1
% 4.03/0.98  --bmc1_max_bound_default                -1
% 4.03/0.98  --bmc1_symbol_reachability              true
% 4.03/0.98  --bmc1_property_lemmas                  false
% 4.03/0.98  --bmc1_k_induction                      false
% 4.03/0.98  --bmc1_non_equiv_states                 false
% 4.03/0.98  --bmc1_deadlock                         false
% 4.03/0.98  --bmc1_ucm                              false
% 4.03/0.98  --bmc1_add_unsat_core                   none
% 4.03/0.98  --bmc1_unsat_core_children              false
% 4.03/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.03/0.98  --bmc1_out_stat                         full
% 4.03/0.98  --bmc1_ground_init                      false
% 4.03/0.98  --bmc1_pre_inst_next_state              false
% 4.03/0.98  --bmc1_pre_inst_state                   false
% 4.03/0.98  --bmc1_pre_inst_reach_state             false
% 4.03/0.98  --bmc1_out_unsat_core                   false
% 4.03/0.98  --bmc1_aig_witness_out                  false
% 4.03/0.98  --bmc1_verbose                          false
% 4.03/0.98  --bmc1_dump_clauses_tptp                false
% 4.03/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.03/0.98  --bmc1_dump_file                        -
% 4.03/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.03/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.03/0.98  --bmc1_ucm_extend_mode                  1
% 4.03/0.98  --bmc1_ucm_init_mode                    2
% 4.03/0.98  --bmc1_ucm_cone_mode                    none
% 4.03/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.03/0.98  --bmc1_ucm_relax_model                  4
% 4.03/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.03/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.03/0.98  --bmc1_ucm_layered_model                none
% 4.03/0.98  --bmc1_ucm_max_lemma_size               10
% 4.03/0.98  
% 4.03/0.98  ------ AIG Options
% 4.03/0.98  
% 4.03/0.98  --aig_mode                              false
% 4.03/0.98  
% 4.03/0.98  ------ Instantiation Options
% 4.03/0.98  
% 4.03/0.98  --instantiation_flag                    true
% 4.03/0.98  --inst_sos_flag                         false
% 4.03/0.98  --inst_sos_phase                        true
% 4.03/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.03/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.03/0.98  --inst_lit_sel_side                     none
% 4.03/0.98  --inst_solver_per_active                1400
% 4.03/0.98  --inst_solver_calls_frac                1.
% 4.03/0.98  --inst_passive_queue_type               priority_queues
% 4.03/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.03/0.98  --inst_passive_queues_freq              [25;2]
% 4.03/0.98  --inst_dismatching                      true
% 4.03/0.98  --inst_eager_unprocessed_to_passive     true
% 4.03/0.98  --inst_prop_sim_given                   true
% 4.03/0.98  --inst_prop_sim_new                     false
% 4.03/0.98  --inst_subs_new                         false
% 4.03/0.98  --inst_eq_res_simp                      false
% 4.03/0.98  --inst_subs_given                       false
% 4.03/0.98  --inst_orphan_elimination               true
% 4.03/0.98  --inst_learning_loop_flag               true
% 4.03/0.98  --inst_learning_start                   3000
% 4.03/0.98  --inst_learning_factor                  2
% 4.03/0.98  --inst_start_prop_sim_after_learn       3
% 4.03/0.98  --inst_sel_renew                        solver
% 4.03/0.98  --inst_lit_activity_flag                true
% 4.03/0.98  --inst_restr_to_given                   false
% 4.03/0.98  --inst_activity_threshold               500
% 4.03/0.98  --inst_out_proof                        true
% 4.03/0.98  
% 4.03/0.98  ------ Resolution Options
% 4.03/0.98  
% 4.03/0.98  --resolution_flag                       false
% 4.03/0.98  --res_lit_sel                           adaptive
% 4.03/0.98  --res_lit_sel_side                      none
% 4.03/0.98  --res_ordering                          kbo
% 4.03/0.98  --res_to_prop_solver                    active
% 4.03/0.98  --res_prop_simpl_new                    false
% 4.03/0.98  --res_prop_simpl_given                  true
% 4.03/0.98  --res_passive_queue_type                priority_queues
% 4.03/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.03/0.98  --res_passive_queues_freq               [15;5]
% 4.03/0.98  --res_forward_subs                      full
% 4.03/0.98  --res_backward_subs                     full
% 4.03/0.98  --res_forward_subs_resolution           true
% 4.03/0.98  --res_backward_subs_resolution          true
% 4.03/0.98  --res_orphan_elimination                true
% 4.03/0.98  --res_time_limit                        2.
% 4.03/0.98  --res_out_proof                         true
% 4.03/0.98  
% 4.03/0.98  ------ Superposition Options
% 4.03/0.98  
% 4.03/0.98  --superposition_flag                    true
% 4.03/0.98  --sup_passive_queue_type                priority_queues
% 4.03/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.03/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.03/0.98  --demod_completeness_check              fast
% 4.03/0.98  --demod_use_ground                      true
% 4.03/0.98  --sup_to_prop_solver                    passive
% 4.03/0.98  --sup_prop_simpl_new                    true
% 4.03/0.98  --sup_prop_simpl_given                  true
% 4.03/0.98  --sup_fun_splitting                     false
% 4.03/0.98  --sup_smt_interval                      50000
% 4.03/0.98  
% 4.03/0.98  ------ Superposition Simplification Setup
% 4.03/0.98  
% 4.03/0.98  --sup_indices_passive                   []
% 4.03/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.03/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.03/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.03/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.03/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.03/0.98  --sup_full_bw                           [BwDemod]
% 4.03/0.98  --sup_immed_triv                        [TrivRules]
% 4.03/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.03/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.03/0.98  --sup_immed_bw_main                     []
% 4.03/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.03/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.03/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.03/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.03/0.98  
% 4.03/0.98  ------ Combination Options
% 4.03/0.98  
% 4.03/0.98  --comb_res_mult                         3
% 4.03/0.98  --comb_sup_mult                         2
% 4.03/0.98  --comb_inst_mult                        10
% 4.03/0.98  
% 4.03/0.98  ------ Debug Options
% 4.03/0.98  
% 4.03/0.98  --dbg_backtrace                         false
% 4.03/0.98  --dbg_dump_prop_clauses                 false
% 4.03/0.98  --dbg_dump_prop_clauses_file            -
% 4.03/0.98  --dbg_out_stat                          false
% 4.03/0.98  
% 4.03/0.98  
% 4.03/0.98  
% 4.03/0.98  
% 4.03/0.98  ------ Proving...
% 4.03/0.98  
% 4.03/0.98  
% 4.03/0.98  % SZS status Theorem for theBenchmark.p
% 4.03/0.98  
% 4.03/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 4.03/0.98  
% 4.03/0.98  fof(f7,conjecture,(
% 4.03/0.98    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)))))))),
% 4.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.03/0.98  
% 4.03/0.98  fof(f8,negated_conjecture,(
% 4.03/0.98    ~! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)))))))),
% 4.03/0.98    inference(negated_conjecture,[],[f7])).
% 4.03/0.98  
% 4.03/0.98  fof(f20,plain,(
% 4.03/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,X1,X2)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)))),
% 4.03/0.98    inference(ennf_transformation,[],[f8])).
% 4.03/0.98  
% 4.03/0.98  fof(f21,plain,(
% 4.03/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0))),
% 4.03/0.98    inference(flattening,[],[f20])).
% 4.03/0.98  
% 4.03/0.98  fof(f38,plain,(
% 4.03/0.98    ( ! [X2,X0,X1] : (? [X3] : (~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,k2_lattices(X0,X1,sK8),k2_lattices(X0,X2,sK8)) & r1_lattices(X0,X1,X2) & m1_subset_1(sK8,u1_struct_0(X0)))) )),
% 4.03/0.98    introduced(choice_axiom,[])).
% 4.03/0.98  
% 4.03/0.98  fof(f37,plain,(
% 4.03/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,sK7,X3)) & r1_lattices(X0,X1,sK7) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK7,u1_struct_0(X0)))) )),
% 4.03/0.98    introduced(choice_axiom,[])).
% 4.03/0.98  
% 4.03/0.98  fof(f36,plain,(
% 4.03/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~r1_lattices(X0,k2_lattices(X0,sK6,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,sK6,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 4.03/0.98    introduced(choice_axiom,[])).
% 4.03/0.98  
% 4.03/0.98  fof(f35,plain,(
% 4.03/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_lattices(sK5,k2_lattices(sK5,X1,X3),k2_lattices(sK5,X2,X3)) & r1_lattices(sK5,X1,X2) & m1_subset_1(X3,u1_struct_0(sK5))) & m1_subset_1(X2,u1_struct_0(sK5))) & m1_subset_1(X1,u1_struct_0(sK5))) & l3_lattices(sK5) & v9_lattices(sK5) & v8_lattices(sK5) & v7_lattices(sK5) & ~v2_struct_0(sK5))),
% 4.03/0.98    introduced(choice_axiom,[])).
% 4.03/0.98  
% 4.03/0.98  fof(f39,plain,(
% 4.03/0.98    (((~r1_lattices(sK5,k2_lattices(sK5,sK6,sK8),k2_lattices(sK5,sK7,sK8)) & r1_lattices(sK5,sK6,sK7) & m1_subset_1(sK8,u1_struct_0(sK5))) & m1_subset_1(sK7,u1_struct_0(sK5))) & m1_subset_1(sK6,u1_struct_0(sK5))) & l3_lattices(sK5) & v9_lattices(sK5) & v8_lattices(sK5) & v7_lattices(sK5) & ~v2_struct_0(sK5)),
% 4.03/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f21,f38,f37,f36,f35])).
% 4.03/0.98  
% 4.03/0.98  fof(f63,plain,(
% 4.03/0.98    m1_subset_1(sK8,u1_struct_0(sK5))),
% 4.03/0.98    inference(cnf_transformation,[],[f39])).
% 4.03/0.98  
% 4.03/0.98  fof(f62,plain,(
% 4.03/0.98    m1_subset_1(sK7,u1_struct_0(sK5))),
% 4.03/0.98    inference(cnf_transformation,[],[f39])).
% 4.03/0.98  
% 4.03/0.98  fof(f4,axiom,(
% 4.03/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 4.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.03/0.98  
% 4.03/0.98  fof(f15,plain,(
% 4.03/0.98    ! [X0,X1,X2] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)))),
% 4.03/0.98    inference(ennf_transformation,[],[f4])).
% 4.03/0.98  
% 4.03/0.98  fof(f16,plain,(
% 4.03/0.98    ! [X0,X1,X2] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 4.03/0.98    inference(flattening,[],[f15])).
% 4.03/0.98  
% 4.03/0.98  fof(f51,plain,(
% 4.03/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 4.03/0.98    inference(cnf_transformation,[],[f16])).
% 4.03/0.98  
% 4.03/0.98  fof(f56,plain,(
% 4.03/0.98    ~v2_struct_0(sK5)),
% 4.03/0.98    inference(cnf_transformation,[],[f39])).
% 4.03/0.98  
% 4.03/0.98  fof(f60,plain,(
% 4.03/0.98    l3_lattices(sK5)),
% 4.03/0.98    inference(cnf_transformation,[],[f39])).
% 4.03/0.98  
% 4.03/0.98  fof(f5,axiom,(
% 4.03/0.98    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 4.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.03/0.98  
% 4.03/0.98  fof(f17,plain,(
% 4.03/0.98    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 4.03/0.98    inference(ennf_transformation,[],[f5])).
% 4.03/0.98  
% 4.03/0.98  fof(f52,plain,(
% 4.03/0.98    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 4.03/0.98    inference(cnf_transformation,[],[f17])).
% 4.03/0.98  
% 4.03/0.98  fof(f61,plain,(
% 4.03/0.98    m1_subset_1(sK6,u1_struct_0(sK5))),
% 4.03/0.98    inference(cnf_transformation,[],[f39])).
% 4.03/0.98  
% 4.03/0.98  fof(f3,axiom,(
% 4.03/0.98    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 4.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.03/0.98  
% 4.03/0.98  fof(f13,plain,(
% 4.03/0.98    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 4.03/0.98    inference(ennf_transformation,[],[f3])).
% 4.03/0.98  
% 4.03/0.98  fof(f14,plain,(
% 4.03/0.98    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.03/0.98    inference(flattening,[],[f13])).
% 4.03/0.98  
% 4.03/0.98  fof(f29,plain,(
% 4.03/0.98    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.03/0.98    inference(nnf_transformation,[],[f14])).
% 4.03/0.98  
% 4.03/0.98  fof(f30,plain,(
% 4.03/0.98    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.03/0.98    inference(rectify,[],[f29])).
% 4.03/0.98  
% 4.03/0.98  fof(f32,plain,(
% 4.03/0.98    ( ! [X1] : (! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (k1_lattices(X0,k2_lattices(X0,X1,sK4(X0)),sK4(X0)) != sK4(X0) & m1_subset_1(sK4(X0),u1_struct_0(X0))))) )),
% 4.03/0.98    introduced(choice_axiom,[])).
% 4.03/0.98  
% 4.03/0.98  fof(f31,plain,(
% 4.03/0.98    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 4.03/0.98    introduced(choice_axiom,[])).
% 4.03/0.98  
% 4.03/0.98  fof(f33,plain,(
% 4.03/0.98    ! [X0] : (((v8_lattices(X0) | ((k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0)) != sK4(X0) & m1_subset_1(sK4(X0),u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.03/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f30,f32,f31])).
% 4.03/0.98  
% 4.03/0.98  fof(f47,plain,(
% 4.03/0.98    ( ! [X4,X0,X3] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v8_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 4.03/0.98    inference(cnf_transformation,[],[f33])).
% 4.03/0.98  
% 4.03/0.98  fof(f58,plain,(
% 4.03/0.98    v8_lattices(sK5)),
% 4.03/0.98    inference(cnf_transformation,[],[f39])).
% 4.03/0.98  
% 4.03/0.98  fof(f2,axiom,(
% 4.03/0.98    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v7_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3))))))),
% 4.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.03/0.98  
% 4.03/0.98  fof(f11,plain,(
% 4.03/0.98    ! [X0] : ((v7_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 4.03/0.98    inference(ennf_transformation,[],[f2])).
% 4.03/0.98  
% 4.03/0.98  fof(f12,plain,(
% 4.03/0.98    ! [X0] : ((v7_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 4.03/0.98    inference(flattening,[],[f11])).
% 4.03/0.98  
% 4.03/0.98  fof(f23,plain,(
% 4.03/0.98    ! [X0] : (((v7_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v7_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 4.03/0.98    inference(nnf_transformation,[],[f12])).
% 4.03/0.98  
% 4.03/0.98  fof(f24,plain,(
% 4.03/0.98    ! [X0] : (((v7_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v7_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 4.03/0.98    inference(rectify,[],[f23])).
% 4.03/0.98  
% 4.03/0.98  fof(f27,plain,(
% 4.03/0.98    ( ! [X2,X1] : (! [X0] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) => (k2_lattices(X0,X1,k2_lattices(X0,X2,sK2(X0))) != k2_lattices(X0,k2_lattices(X0,X1,X2),sK2(X0)) & m1_subset_1(sK2(X0),u1_struct_0(X0))))) )),
% 4.03/0.98    introduced(choice_axiom,[])).
% 4.03/0.98  
% 4.03/0.98  fof(f26,plain,(
% 4.03/0.98    ( ! [X1] : (! [X0] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,sK1(X0),X3)) != k2_lattices(X0,k2_lattices(X0,X1,sK1(X0)),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK1(X0),u1_struct_0(X0))))) )),
% 4.03/0.98    introduced(choice_axiom,[])).
% 4.03/0.98  
% 4.03/0.98  fof(f25,plain,(
% 4.03/0.98    ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k2_lattices(X0,k2_lattices(X0,sK0(X0),X2),X3) != k2_lattices(X0,sK0(X0),k2_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0))))),
% 4.03/0.98    introduced(choice_axiom,[])).
% 4.03/0.98  
% 4.03/0.98  fof(f28,plain,(
% 4.03/0.98    ! [X0] : (((v7_lattices(X0) | (((k2_lattices(X0,k2_lattices(X0,sK0(X0),sK1(X0)),sK2(X0)) != k2_lattices(X0,sK0(X0),k2_lattices(X0,sK1(X0),sK2(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))) & m1_subset_1(sK1(X0),u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v7_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 4.03/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).
% 4.03/0.98  
% 4.03/0.98  fof(f42,plain,(
% 4.03/0.98    ( ! [X6,X4,X0,X5] : (k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v7_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 4.03/0.98    inference(cnf_transformation,[],[f28])).
% 4.03/0.98  
% 4.03/0.98  fof(f57,plain,(
% 4.03/0.98    v7_lattices(sK5)),
% 4.03/0.98    inference(cnf_transformation,[],[f39])).
% 4.03/0.98  
% 4.03/0.98  fof(f64,plain,(
% 4.03/0.98    r1_lattices(sK5,sK6,sK7)),
% 4.03/0.98    inference(cnf_transformation,[],[f39])).
% 4.03/0.98  
% 4.03/0.98  fof(f6,axiom,(
% 4.03/0.98    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 4.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.03/0.98  
% 4.03/0.98  fof(f18,plain,(
% 4.03/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 4.03/0.98    inference(ennf_transformation,[],[f6])).
% 4.03/0.98  
% 4.03/0.98  fof(f19,plain,(
% 4.03/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 4.03/0.98    inference(flattening,[],[f18])).
% 4.03/0.98  
% 4.03/0.98  fof(f34,plain,(
% 4.03/0.98    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 4.03/0.98    inference(nnf_transformation,[],[f19])).
% 4.03/0.98  
% 4.03/0.98  fof(f54,plain,(
% 4.03/0.98    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 4.03/0.98    inference(cnf_transformation,[],[f34])).
% 4.03/0.98  
% 4.03/0.98  fof(f59,plain,(
% 4.03/0.98    v9_lattices(sK5)),
% 4.03/0.98    inference(cnf_transformation,[],[f39])).
% 4.03/0.98  
% 4.03/0.98  fof(f65,plain,(
% 4.03/0.98    ~r1_lattices(sK5,k2_lattices(sK5,sK6,sK8),k2_lattices(sK5,sK7,sK8))),
% 4.03/0.98    inference(cnf_transformation,[],[f39])).
% 4.03/0.98  
% 4.03/0.98  fof(f53,plain,(
% 4.03/0.98    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 4.03/0.98    inference(cnf_transformation,[],[f17])).
% 4.03/0.98  
% 4.03/0.98  fof(f1,axiom,(
% 4.03/0.98    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 4.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.03/0.98  
% 4.03/0.98  fof(f9,plain,(
% 4.03/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 4.03/0.98    inference(ennf_transformation,[],[f1])).
% 4.03/0.98  
% 4.03/0.98  fof(f10,plain,(
% 4.03/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 4.03/0.98    inference(flattening,[],[f9])).
% 4.03/0.98  
% 4.03/0.98  fof(f22,plain,(
% 4.03/0.98    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 4.03/0.98    inference(nnf_transformation,[],[f10])).
% 4.03/0.98  
% 4.03/0.98  fof(f41,plain,(
% 4.03/0.98    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 4.03/0.98    inference(cnf_transformation,[],[f22])).
% 4.03/0.98  
% 4.03/0.98  cnf(c_18,negated_conjecture,
% 4.03/0.98      ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
% 4.03/0.98      inference(cnf_transformation,[],[f63]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_736,negated_conjecture,
% 4.03/0.98      ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
% 4.03/0.98      inference(subtyping,[status(esa)],[c_18]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_911,plain,
% 4.03/0.98      ( m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
% 4.03/0.98      inference(predicate_to_equality,[status(thm)],[c_736]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_19,negated_conjecture,
% 4.03/0.98      ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 4.03/0.98      inference(cnf_transformation,[],[f62]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_735,negated_conjecture,
% 4.03/0.98      ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 4.03/0.98      inference(subtyping,[status(esa)],[c_19]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_912,plain,
% 4.03/0.98      ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
% 4.03/0.98      inference(predicate_to_equality,[status(thm)],[c_735]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_11,plain,
% 4.03/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 4.03/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 4.03/0.98      | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
% 4.03/0.98      | ~ l1_lattices(X1)
% 4.03/0.98      | v2_struct_0(X1) ),
% 4.03/0.98      inference(cnf_transformation,[],[f51]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_25,negated_conjecture,
% 4.03/0.98      ( ~ v2_struct_0(sK5) ),
% 4.03/0.98      inference(cnf_transformation,[],[f56]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_491,plain,
% 4.03/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 4.03/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 4.03/0.98      | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
% 4.03/0.98      | ~ l1_lattices(X1)
% 4.03/0.98      | sK5 != X1 ),
% 4.03/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_492,plain,
% 4.03/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 4.03/0.98      | m1_subset_1(k2_lattices(sK5,X0,X1),u1_struct_0(sK5))
% 4.03/0.98      | ~ l1_lattices(sK5) ),
% 4.03/0.98      inference(unflattening,[status(thm)],[c_491]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_21,negated_conjecture,
% 4.03/0.98      ( l3_lattices(sK5) ),
% 4.03/0.98      inference(cnf_transformation,[],[f60]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_13,plain,
% 4.03/0.98      ( ~ l3_lattices(X0) | l1_lattices(X0) ),
% 4.03/0.98      inference(cnf_transformation,[],[f52]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_43,plain,
% 4.03/0.98      ( ~ l3_lattices(sK5) | l1_lattices(sK5) ),
% 4.03/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_496,plain,
% 4.03/0.98      ( m1_subset_1(k2_lattices(sK5,X0,X1),u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 4.03/0.98      inference(global_propositional_subsumption,
% 4.03/0.98                [status(thm)],
% 4.03/0.98                [c_492,c_21,c_43]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_497,plain,
% 4.03/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 4.03/0.98      | m1_subset_1(k2_lattices(sK5,X1,X0),u1_struct_0(sK5)) ),
% 4.03/0.98      inference(renaming,[status(thm)],[c_496]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_732,plain,
% 4.03/0.98      ( ~ m1_subset_1(X0_49,u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(X1_49,u1_struct_0(sK5))
% 4.03/0.98      | m1_subset_1(k2_lattices(sK5,X1_49,X0_49),u1_struct_0(sK5)) ),
% 4.03/0.98      inference(subtyping,[status(esa)],[c_497]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_915,plain,
% 4.03/0.98      ( m1_subset_1(X0_49,u1_struct_0(sK5)) != iProver_top
% 4.03/0.98      | m1_subset_1(X1_49,u1_struct_0(sK5)) != iProver_top
% 4.03/0.98      | m1_subset_1(k2_lattices(sK5,X1_49,X0_49),u1_struct_0(sK5)) = iProver_top ),
% 4.03/0.98      inference(predicate_to_equality,[status(thm)],[c_732]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_20,negated_conjecture,
% 4.03/0.98      ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 4.03/0.98      inference(cnf_transformation,[],[f61]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_734,negated_conjecture,
% 4.03/0.98      ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 4.03/0.98      inference(subtyping,[status(esa)],[c_20]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_913,plain,
% 4.03/0.98      ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
% 4.03/0.98      inference(predicate_to_equality,[status(thm)],[c_734]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_10,plain,
% 4.03/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 4.03/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 4.03/0.98      | ~ l3_lattices(X1)
% 4.03/0.98      | ~ v8_lattices(X1)
% 4.03/0.98      | v2_struct_0(X1)
% 4.03/0.98      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 ),
% 4.03/0.98      inference(cnf_transformation,[],[f47]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_446,plain,
% 4.03/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 4.03/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 4.03/0.98      | ~ v8_lattices(X1)
% 4.03/0.98      | v2_struct_0(X1)
% 4.03/0.98      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
% 4.03/0.98      | sK5 != X1 ),
% 4.03/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_447,plain,
% 4.03/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 4.03/0.98      | ~ v8_lattices(sK5)
% 4.03/0.98      | v2_struct_0(sK5)
% 4.03/0.98      | k1_lattices(sK5,k2_lattices(sK5,X0,X1),X1) = X1 ),
% 4.03/0.98      inference(unflattening,[status(thm)],[c_446]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_23,negated_conjecture,
% 4.03/0.98      ( v8_lattices(sK5) ),
% 4.03/0.98      inference(cnf_transformation,[],[f58]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_451,plain,
% 4.03/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 4.03/0.98      | k1_lattices(sK5,k2_lattices(sK5,X0,X1),X1) = X1 ),
% 4.03/0.98      inference(global_propositional_subsumption,
% 4.03/0.98                [status(thm)],
% 4.03/0.98                [c_447,c_25,c_23]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_452,plain,
% 4.03/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 4.03/0.98      | k1_lattices(sK5,k2_lattices(sK5,X1,X0),X0) = X0 ),
% 4.03/0.98      inference(renaming,[status(thm)],[c_451]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_733,plain,
% 4.03/0.98      ( ~ m1_subset_1(X0_49,u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(X1_49,u1_struct_0(sK5))
% 4.03/0.98      | k1_lattices(sK5,k2_lattices(sK5,X1_49,X0_49),X0_49) = X0_49 ),
% 4.03/0.98      inference(subtyping,[status(esa)],[c_452]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_914,plain,
% 4.03/0.98      ( k1_lattices(sK5,k2_lattices(sK5,X0_49,X1_49),X1_49) = X1_49
% 4.03/0.98      | m1_subset_1(X1_49,u1_struct_0(sK5)) != iProver_top
% 4.03/0.98      | m1_subset_1(X0_49,u1_struct_0(sK5)) != iProver_top ),
% 4.03/0.98      inference(predicate_to_equality,[status(thm)],[c_733]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_1131,plain,
% 4.03/0.98      ( k1_lattices(sK5,k2_lattices(sK5,sK6,X0_49),X0_49) = X0_49
% 4.03/0.98      | m1_subset_1(X0_49,u1_struct_0(sK5)) != iProver_top ),
% 4.03/0.98      inference(superposition,[status(thm)],[c_913,c_914]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_1723,plain,
% 4.03/0.98      ( k1_lattices(sK5,k2_lattices(sK5,sK6,k2_lattices(sK5,X0_49,X1_49)),k2_lattices(sK5,X0_49,X1_49)) = k2_lattices(sK5,X0_49,X1_49)
% 4.03/0.98      | m1_subset_1(X1_49,u1_struct_0(sK5)) != iProver_top
% 4.03/0.98      | m1_subset_1(X0_49,u1_struct_0(sK5)) != iProver_top ),
% 4.03/0.98      inference(superposition,[status(thm)],[c_915,c_1131]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_10970,plain,
% 4.03/0.98      ( k1_lattices(sK5,k2_lattices(sK5,sK6,k2_lattices(sK5,sK7,X0_49)),k2_lattices(sK5,sK7,X0_49)) = k2_lattices(sK5,sK7,X0_49)
% 4.03/0.98      | m1_subset_1(X0_49,u1_struct_0(sK5)) != iProver_top ),
% 4.03/0.98      inference(superposition,[status(thm)],[c_912,c_1723]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_12385,plain,
% 4.03/0.98      ( k1_lattices(sK5,k2_lattices(sK5,sK6,k2_lattices(sK5,sK7,sK8)),k2_lattices(sK5,sK7,sK8)) = k2_lattices(sK5,sK7,sK8) ),
% 4.03/0.98      inference(superposition,[status(thm)],[c_911,c_10970]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_6,plain,
% 4.03/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 4.03/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 4.03/0.98      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 4.03/0.98      | ~ l1_lattices(X1)
% 4.03/0.98      | ~ v7_lattices(X1)
% 4.03/0.98      | v2_struct_0(X1)
% 4.03/0.98      | k2_lattices(X1,k2_lattices(X1,X3,X2),X0) = k2_lattices(X1,X3,k2_lattices(X1,X2,X0)) ),
% 4.03/0.98      inference(cnf_transformation,[],[f42]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_512,plain,
% 4.03/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 4.03/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 4.03/0.98      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 4.03/0.98      | ~ l1_lattices(X1)
% 4.03/0.98      | ~ v7_lattices(X1)
% 4.03/0.98      | k2_lattices(X1,X3,k2_lattices(X1,X2,X0)) = k2_lattices(X1,k2_lattices(X1,X3,X2),X0)
% 4.03/0.98      | sK5 != X1 ),
% 4.03/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_25]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_513,plain,
% 4.03/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 4.03/0.98      | ~ l1_lattices(sK5)
% 4.03/0.98      | ~ v7_lattices(sK5)
% 4.03/0.98      | k2_lattices(sK5,X2,k2_lattices(sK5,X0,X1)) = k2_lattices(sK5,k2_lattices(sK5,X2,X0),X1) ),
% 4.03/0.98      inference(unflattening,[status(thm)],[c_512]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_24,negated_conjecture,
% 4.03/0.98      ( v7_lattices(sK5) ),
% 4.03/0.98      inference(cnf_transformation,[],[f57]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_517,plain,
% 4.03/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 4.03/0.98      | k2_lattices(sK5,X2,k2_lattices(sK5,X0,X1)) = k2_lattices(sK5,k2_lattices(sK5,X2,X0),X1) ),
% 4.03/0.98      inference(global_propositional_subsumption,
% 4.03/0.98                [status(thm)],
% 4.03/0.98                [c_513,c_24,c_21,c_43]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_518,plain,
% 4.03/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 4.03/0.98      | k2_lattices(sK5,X1,k2_lattices(sK5,X2,X0)) = k2_lattices(sK5,k2_lattices(sK5,X1,X2),X0) ),
% 4.03/0.98      inference(renaming,[status(thm)],[c_517]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_731,plain,
% 4.03/0.98      ( ~ m1_subset_1(X0_49,u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(X1_49,u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(X2_49,u1_struct_0(sK5))
% 4.03/0.98      | k2_lattices(sK5,X1_49,k2_lattices(sK5,X2_49,X0_49)) = k2_lattices(sK5,k2_lattices(sK5,X1_49,X2_49),X0_49) ),
% 4.03/0.98      inference(subtyping,[status(esa)],[c_518]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_916,plain,
% 4.03/0.98      ( k2_lattices(sK5,X0_49,k2_lattices(sK5,X1_49,X2_49)) = k2_lattices(sK5,k2_lattices(sK5,X0_49,X1_49),X2_49)
% 4.03/0.98      | m1_subset_1(X2_49,u1_struct_0(sK5)) != iProver_top
% 4.03/0.98      | m1_subset_1(X0_49,u1_struct_0(sK5)) != iProver_top
% 4.03/0.98      | m1_subset_1(X1_49,u1_struct_0(sK5)) != iProver_top ),
% 4.03/0.98      inference(predicate_to_equality,[status(thm)],[c_731]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_2068,plain,
% 4.03/0.98      ( k2_lattices(sK5,k2_lattices(sK5,sK6,X0_49),X1_49) = k2_lattices(sK5,sK6,k2_lattices(sK5,X0_49,X1_49))
% 4.03/0.98      | m1_subset_1(X0_49,u1_struct_0(sK5)) != iProver_top
% 4.03/0.98      | m1_subset_1(X1_49,u1_struct_0(sK5)) != iProver_top ),
% 4.03/0.98      inference(superposition,[status(thm)],[c_913,c_916]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_5223,plain,
% 4.03/0.98      ( k2_lattices(sK5,sK6,k2_lattices(sK5,sK7,X0_49)) = k2_lattices(sK5,k2_lattices(sK5,sK6,sK7),X0_49)
% 4.03/0.98      | m1_subset_1(X0_49,u1_struct_0(sK5)) != iProver_top ),
% 4.03/0.98      inference(superposition,[status(thm)],[c_912,c_2068]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_17,negated_conjecture,
% 4.03/0.98      ( r1_lattices(sK5,sK6,sK7) ),
% 4.03/0.98      inference(cnf_transformation,[],[f64]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_15,plain,
% 4.03/0.98      ( ~ r1_lattices(X0,X1,X2)
% 4.03/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.03/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 4.03/0.98      | ~ v9_lattices(X0)
% 4.03/0.98      | ~ l3_lattices(X0)
% 4.03/0.98      | ~ v8_lattices(X0)
% 4.03/0.98      | v2_struct_0(X0)
% 4.03/0.98      | k2_lattices(X0,X1,X2) = X1 ),
% 4.03/0.98      inference(cnf_transformation,[],[f54]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_22,negated_conjecture,
% 4.03/0.98      ( v9_lattices(sK5) ),
% 4.03/0.98      inference(cnf_transformation,[],[f59]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_327,plain,
% 4.03/0.98      ( ~ r1_lattices(X0,X1,X2)
% 4.03/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.03/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 4.03/0.98      | ~ l3_lattices(X0)
% 4.03/0.98      | ~ v8_lattices(X0)
% 4.03/0.98      | v2_struct_0(X0)
% 4.03/0.98      | k2_lattices(X0,X1,X2) = X1
% 4.03/0.98      | sK5 != X0 ),
% 4.03/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_328,plain,
% 4.03/0.98      ( ~ r1_lattices(sK5,X0,X1)
% 4.03/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 4.03/0.98      | ~ l3_lattices(sK5)
% 4.03/0.98      | ~ v8_lattices(sK5)
% 4.03/0.98      | v2_struct_0(sK5)
% 4.03/0.98      | k2_lattices(sK5,X0,X1) = X0 ),
% 4.03/0.98      inference(unflattening,[status(thm)],[c_327]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_332,plain,
% 4.03/0.98      ( ~ m1_subset_1(X1,u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 4.03/0.98      | ~ r1_lattices(sK5,X0,X1)
% 4.03/0.98      | k2_lattices(sK5,X0,X1) = X0 ),
% 4.03/0.98      inference(global_propositional_subsumption,
% 4.03/0.98                [status(thm)],
% 4.03/0.98                [c_328,c_25,c_23,c_21]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_333,plain,
% 4.03/0.98      ( ~ r1_lattices(sK5,X0,X1)
% 4.03/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 4.03/0.98      | k2_lattices(sK5,X0,X1) = X0 ),
% 4.03/0.98      inference(renaming,[status(thm)],[c_332]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_625,plain,
% 4.03/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 4.03/0.98      | k2_lattices(sK5,X1,X0) = X1
% 4.03/0.98      | sK7 != X0
% 4.03/0.98      | sK6 != X1
% 4.03/0.98      | sK5 != sK5 ),
% 4.03/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_333]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_626,plain,
% 4.03/0.98      ( ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 4.03/0.98      | k2_lattices(sK5,sK6,sK7) = sK6 ),
% 4.03/0.98      inference(unflattening,[status(thm)],[c_625]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_628,plain,
% 4.03/0.98      ( k2_lattices(sK5,sK6,sK7) = sK6 ),
% 4.03/0.98      inference(global_propositional_subsumption,
% 4.03/0.98                [status(thm)],
% 4.03/0.98                [c_626,c_20,c_19]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_725,plain,
% 4.03/0.98      ( k2_lattices(sK5,sK6,sK7) = sK6 ),
% 4.03/0.98      inference(subtyping,[status(esa)],[c_628]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_5240,plain,
% 4.03/0.98      ( k2_lattices(sK5,sK6,k2_lattices(sK5,sK7,X0_49)) = k2_lattices(sK5,sK6,X0_49)
% 4.03/0.98      | m1_subset_1(X0_49,u1_struct_0(sK5)) != iProver_top ),
% 4.03/0.98      inference(light_normalisation,[status(thm)],[c_5223,c_725]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_5753,plain,
% 4.03/0.98      ( k2_lattices(sK5,sK6,k2_lattices(sK5,sK7,sK8)) = k2_lattices(sK5,sK6,sK8) ),
% 4.03/0.98      inference(superposition,[status(thm)],[c_911,c_5240]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_12402,plain,
% 4.03/0.98      ( k1_lattices(sK5,k2_lattices(sK5,sK6,sK8),k2_lattices(sK5,sK7,sK8)) = k2_lattices(sK5,sK7,sK8) ),
% 4.03/0.98      inference(light_normalisation,[status(thm)],[c_12385,c_5753]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_1072,plain,
% 4.03/0.98      ( m1_subset_1(k2_lattices(sK5,sK6,sK8),u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 4.03/0.98      inference(instantiation,[status(thm)],[c_732]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_1004,plain,
% 4.03/0.98      ( m1_subset_1(k2_lattices(sK5,sK7,sK8),u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(sK8,u1_struct_0(sK5)) ),
% 4.03/0.98      inference(instantiation,[status(thm)],[c_732]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_16,negated_conjecture,
% 4.03/0.98      ( ~ r1_lattices(sK5,k2_lattices(sK5,sK6,sK8),k2_lattices(sK5,sK7,sK8)) ),
% 4.03/0.98      inference(cnf_transformation,[],[f65]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_12,plain,
% 4.03/0.98      ( ~ l3_lattices(X0) | l2_lattices(X0) ),
% 4.03/0.98      inference(cnf_transformation,[],[f53]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_0,plain,
% 4.03/0.98      ( r1_lattices(X0,X1,X2)
% 4.03/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.03/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 4.03/0.98      | v2_struct_0(X0)
% 4.03/0.98      | ~ l2_lattices(X0)
% 4.03/0.98      | k1_lattices(X0,X1,X2) != X2 ),
% 4.03/0.98      inference(cnf_transformation,[],[f41]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_290,plain,
% 4.03/0.98      ( r1_lattices(X0,X1,X2)
% 4.03/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.03/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 4.03/0.98      | ~ l3_lattices(X0)
% 4.03/0.98      | v2_struct_0(X0)
% 4.03/0.98      | k1_lattices(X0,X1,X2) != X2 ),
% 4.03/0.98      inference(resolution,[status(thm)],[c_12,c_0]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_385,plain,
% 4.03/0.98      ( r1_lattices(X0,X1,X2)
% 4.03/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.03/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 4.03/0.98      | v2_struct_0(X0)
% 4.03/0.98      | k1_lattices(X0,X1,X2) != X2
% 4.03/0.98      | sK5 != X0 ),
% 4.03/0.98      inference(resolution_lifted,[status(thm)],[c_290,c_21]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_386,plain,
% 4.03/0.98      ( r1_lattices(sK5,X0,X1)
% 4.03/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 4.03/0.98      | v2_struct_0(sK5)
% 4.03/0.98      | k1_lattices(sK5,X0,X1) != X1 ),
% 4.03/0.98      inference(unflattening,[status(thm)],[c_385]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_390,plain,
% 4.03/0.98      ( ~ m1_subset_1(X1,u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 4.03/0.98      | r1_lattices(sK5,X0,X1)
% 4.03/0.98      | k1_lattices(sK5,X0,X1) != X1 ),
% 4.03/0.98      inference(global_propositional_subsumption,
% 4.03/0.98                [status(thm)],
% 4.03/0.98                [c_386,c_25]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_391,plain,
% 4.03/0.98      ( r1_lattices(sK5,X0,X1)
% 4.03/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 4.03/0.98      | k1_lattices(sK5,X0,X1) != X1 ),
% 4.03/0.98      inference(renaming,[status(thm)],[c_390]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_591,plain,
% 4.03/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 4.03/0.98      | k2_lattices(sK5,sK7,sK8) != X0
% 4.03/0.98      | k2_lattices(sK5,sK6,sK8) != X1
% 4.03/0.98      | k1_lattices(sK5,X1,X0) != X0
% 4.03/0.98      | sK5 != sK5 ),
% 4.03/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_391]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_592,plain,
% 4.03/0.98      ( ~ m1_subset_1(k2_lattices(sK5,sK7,sK8),u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(k2_lattices(sK5,sK6,sK8),u1_struct_0(sK5))
% 4.03/0.98      | k1_lattices(sK5,k2_lattices(sK5,sK6,sK8),k2_lattices(sK5,sK7,sK8)) != k2_lattices(sK5,sK7,sK8) ),
% 4.03/0.98      inference(unflattening,[status(thm)],[c_591]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(c_728,plain,
% 4.03/0.98      ( ~ m1_subset_1(k2_lattices(sK5,sK7,sK8),u1_struct_0(sK5))
% 4.03/0.98      | ~ m1_subset_1(k2_lattices(sK5,sK6,sK8),u1_struct_0(sK5))
% 4.03/0.98      | k1_lattices(sK5,k2_lattices(sK5,sK6,sK8),k2_lattices(sK5,sK7,sK8)) != k2_lattices(sK5,sK7,sK8) ),
% 4.03/0.98      inference(subtyping,[status(esa)],[c_592]) ).
% 4.03/0.98  
% 4.03/0.98  cnf(contradiction,plain,
% 4.03/0.98      ( $false ),
% 4.03/0.98      inference(minisat,
% 4.03/0.98                [status(thm)],
% 4.03/0.98                [c_12402,c_1072,c_1004,c_728,c_18,c_19,c_20]) ).
% 4.03/0.98  
% 4.03/0.98  
% 4.03/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 4.03/0.98  
% 4.03/0.98  ------                               Statistics
% 4.03/0.98  
% 4.03/0.98  ------ General
% 4.03/0.98  
% 4.03/0.98  abstr_ref_over_cycles:                  0
% 4.03/0.98  abstr_ref_under_cycles:                 0
% 4.03/0.98  gc_basic_clause_elim:                   0
% 4.03/0.98  forced_gc_time:                         0
% 4.03/0.98  parsing_time:                           0.02
% 4.03/0.98  unif_index_cands_time:                  0.
% 4.03/0.98  unif_index_add_time:                    0.
% 4.03/0.98  orderings_time:                         0.
% 4.03/0.98  out_proof_time:                         0.008
% 4.03/0.98  total_time:                             0.431
% 4.03/0.98  num_of_symbols:                         52
% 4.03/0.98  num_of_terms:                           15443
% 4.03/0.98  
% 4.03/0.98  ------ Preprocessing
% 4.03/0.98  
% 4.03/0.98  num_of_splits:                          0
% 4.03/0.98  num_of_split_atoms:                     0
% 4.03/0.98  num_of_reused_defs:                     0
% 4.03/0.98  num_eq_ax_congr_red:                    12
% 4.03/0.98  num_of_sem_filtered_clauses:            1
% 4.03/0.98  num_of_subtypes:                        3
% 4.03/0.98  monotx_restored_types:                  0
% 4.03/0.98  sat_num_of_epr_types:                   0
% 4.03/0.98  sat_num_of_non_cyclic_types:            0
% 4.03/0.98  sat_guarded_non_collapsed_types:        1
% 4.03/0.98  num_pure_diseq_elim:                    0
% 4.03/0.98  simp_replaced_by:                       0
% 4.03/0.98  res_preprocessed:                       76
% 4.03/0.98  prep_upred:                             0
% 4.03/0.98  prep_unflattend:                        23
% 4.03/0.98  smt_new_axioms:                         0
% 4.03/0.98  pred_elim_cands:                        1
% 4.03/0.98  pred_elim:                              8
% 4.03/0.98  pred_elim_cl:                           13
% 4.03/0.98  pred_elim_cycles:                       10
% 4.03/0.98  merged_defs:                            0
% 4.03/0.98  merged_defs_ncl:                        0
% 4.03/0.98  bin_hyper_res:                          0
% 4.03/0.98  prep_cycles:                            4
% 4.03/0.98  pred_elim_time:                         0.02
% 4.03/0.98  splitting_time:                         0.
% 4.03/0.98  sem_filter_time:                        0.
% 4.03/0.98  monotx_time:                            0.
% 4.03/0.98  subtype_inf_time:                       0.
% 4.03/0.98  
% 4.03/0.98  ------ Problem properties
% 4.03/0.98  
% 4.03/0.98  clauses:                                13
% 4.03/0.98  conjectures:                            3
% 4.03/0.98  epr:                                    0
% 4.03/0.98  horn:                                   13
% 4.03/0.98  ground:                                 8
% 4.03/0.98  unary:                                  5
% 4.03/0.98  binary:                                 1
% 4.03/0.98  lits:                                   31
% 4.03/0.98  lits_eq:                                12
% 4.03/0.98  fd_pure:                                0
% 4.03/0.98  fd_pseudo:                              0
% 4.03/0.98  fd_cond:                                0
% 4.03/0.98  fd_pseudo_cond:                         0
% 4.03/0.98  ac_symbols:                             0
% 4.03/0.98  
% 4.03/0.98  ------ Propositional Solver
% 4.03/0.98  
% 4.03/0.98  prop_solver_calls:                      29
% 4.03/0.98  prop_fast_solver_calls:                 693
% 4.03/0.98  smt_solver_calls:                       0
% 4.03/0.98  smt_fast_solver_calls:                  0
% 4.03/0.98  prop_num_of_clauses:                    3546
% 4.03/0.98  prop_preprocess_simplified:             7060
% 4.03/0.98  prop_fo_subsumed:                       21
% 4.03/0.98  prop_solver_time:                       0.
% 4.03/0.98  smt_solver_time:                        0.
% 4.03/0.98  smt_fast_solver_time:                   0.
% 4.03/0.98  prop_fast_solver_time:                  0.
% 4.03/0.98  prop_unsat_core_time:                   0.
% 4.03/0.98  
% 4.03/0.98  ------ QBF
% 4.03/0.98  
% 4.03/0.98  qbf_q_res:                              0
% 4.03/0.98  qbf_num_tautologies:                    0
% 4.03/0.98  qbf_prep_cycles:                        0
% 4.03/0.98  
% 4.03/0.98  ------ BMC1
% 4.03/0.98  
% 4.03/0.98  bmc1_current_bound:                     -1
% 4.03/0.98  bmc1_last_solved_bound:                 -1
% 4.03/0.98  bmc1_unsat_core_size:                   -1
% 4.03/0.98  bmc1_unsat_core_parents_size:           -1
% 4.03/0.98  bmc1_merge_next_fun:                    0
% 4.03/0.98  bmc1_unsat_core_clauses_time:           0.
% 4.03/0.98  
% 4.03/0.98  ------ Instantiation
% 4.03/0.98  
% 4.03/0.98  inst_num_of_clauses:                    1450
% 4.03/0.98  inst_num_in_passive:                    213
% 4.03/0.98  inst_num_in_active:                     507
% 4.03/0.98  inst_num_in_unprocessed:                730
% 4.03/0.98  inst_num_of_loops:                      530
% 4.03/0.98  inst_num_of_learning_restarts:          0
% 4.03/0.98  inst_num_moves_active_passive:          20
% 4.03/0.98  inst_lit_activity:                      0
% 4.03/0.98  inst_lit_activity_moves:                0
% 4.03/0.98  inst_num_tautologies:                   0
% 4.03/0.98  inst_num_prop_implied:                  0
% 4.03/0.98  inst_num_existing_simplified:           0
% 4.03/0.98  inst_num_eq_res_simplified:             0
% 4.03/0.98  inst_num_child_elim:                    0
% 4.03/0.98  inst_num_of_dismatching_blockings:      3111
% 4.03/0.98  inst_num_of_non_proper_insts:           2416
% 4.03/0.98  inst_num_of_duplicates:                 0
% 4.03/0.98  inst_inst_num_from_inst_to_res:         0
% 4.03/0.98  inst_dismatching_checking_time:         0.
% 4.03/0.98  
% 4.03/0.98  ------ Resolution
% 4.03/0.98  
% 4.03/0.98  res_num_of_clauses:                     0
% 4.03/0.98  res_num_in_passive:                     0
% 4.03/0.98  res_num_in_active:                      0
% 4.03/0.98  res_num_of_loops:                       80
% 4.03/0.98  res_forward_subset_subsumed:            78
% 4.03/0.98  res_backward_subset_subsumed:           0
% 4.03/0.98  res_forward_subsumed:                   0
% 4.03/0.98  res_backward_subsumed:                  0
% 4.03/0.98  res_forward_subsumption_resolution:     0
% 4.03/0.98  res_backward_subsumption_resolution:    0
% 4.03/0.98  res_clause_to_clause_subsumption:       733
% 4.03/0.98  res_orphan_elimination:                 0
% 4.03/0.98  res_tautology_del:                      400
% 4.03/0.98  res_num_eq_res_simplified:              1
% 4.03/0.98  res_num_sel_changes:                    0
% 4.03/0.98  res_moves_from_active_to_pass:          0
% 4.03/0.98  
% 4.03/0.98  ------ Superposition
% 4.03/0.98  
% 4.03/0.98  sup_time_total:                         0.
% 4.03/0.98  sup_time_generating:                    0.
% 4.03/0.98  sup_time_sim_full:                      0.
% 4.03/0.98  sup_time_sim_immed:                     0.
% 4.03/0.98  
% 4.03/0.98  sup_num_of_clauses:                     233
% 4.03/0.98  sup_num_in_active:                      105
% 4.03/0.98  sup_num_in_passive:                     128
% 4.03/0.98  sup_num_of_loops:                       104
% 4.03/0.98  sup_fw_superposition:                   185
% 4.03/0.98  sup_bw_superposition:                   59
% 4.03/0.98  sup_immediate_simplified:               51
% 4.03/0.98  sup_given_eliminated:                   0
% 4.03/0.98  comparisons_done:                       0
% 4.03/0.98  comparisons_avoided:                    0
% 4.03/0.98  
% 4.03/0.98  ------ Simplifications
% 4.03/0.98  
% 4.03/0.98  
% 4.03/0.98  sim_fw_subset_subsumed:                 10
% 4.03/0.98  sim_bw_subset_subsumed:                 4
% 4.03/0.98  sim_fw_subsumed:                        3
% 4.03/0.98  sim_bw_subsumed:                        0
% 4.03/0.98  sim_fw_subsumption_res:                 0
% 4.03/0.98  sim_bw_subsumption_res:                 0
% 4.03/0.98  sim_tautology_del:                      3
% 4.03/0.98  sim_eq_tautology_del:                   3
% 4.03/0.98  sim_eq_res_simp:                        0
% 4.03/0.98  sim_fw_demodulated:                     2
% 4.03/0.98  sim_bw_demodulated:                     0
% 4.03/0.98  sim_light_normalised:                   36
% 4.03/0.98  sim_joinable_taut:                      0
% 4.03/0.98  sim_joinable_simp:                      0
% 4.03/0.98  sim_ac_normalised:                      0
% 4.03/0.98  sim_smt_subsumption:                    0
% 4.03/0.98  
%------------------------------------------------------------------------------
