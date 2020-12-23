%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:13 EST 2020

% Result     : Theorem 11.38s
% Output     : CNFRefutation 11.38s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 705 expanded)
%              Number of clauses        :   83 ( 158 expanded)
%              Number of leaves         :   18 ( 253 expanded)
%              Depth                    :   21
%              Number of atoms          :  669 (5289 expanded)
%              Number of equality atoms :  141 ( 241 expanded)
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

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
          & r1_lattices(X0,X1,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,k2_lattices(X0,X1,sK10),k2_lattices(X0,X2,sK10))
        & r1_lattices(X0,X1,X2)
        & m1_subset_1(sK10,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
              & r1_lattices(X0,X1,X2)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,sK9,X3))
            & r1_lattices(X0,X1,sK9)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK9,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
                ( ~ r1_lattices(X0,k2_lattices(X0,sK8,X3),k2_lattices(X0,X2,X3))
                & r1_lattices(X0,sK8,X2)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK8,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
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
                  ( ~ r1_lattices(sK7,k2_lattices(sK7,X1,X3),k2_lattices(sK7,X2,X3))
                  & r1_lattices(sK7,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(sK7)) )
              & m1_subset_1(X2,u1_struct_0(sK7)) )
          & m1_subset_1(X1,u1_struct_0(sK7)) )
      & l3_lattices(sK7)
      & v9_lattices(sK7)
      & v8_lattices(sK7)
      & v7_lattices(sK7)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ~ r1_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10))
    & r1_lattices(sK7,sK8,sK9)
    & m1_subset_1(sK10,u1_struct_0(sK7))
    & m1_subset_1(sK9,u1_struct_0(sK7))
    & m1_subset_1(sK8,u1_struct_0(sK7))
    & l3_lattices(sK7)
    & v9_lattices(sK7)
    & v8_lattices(sK7)
    & v7_lattices(sK7)
    & ~ v2_struct_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f21,f42,f41,f40,f39])).

fof(f69,plain,(
    m1_subset_1(sK10,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f46,plain,(
    ! [X6,X4,X0,X5] :
      ( k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v7_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f62,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,(
    l3_lattices(sK7) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    v7_lattices(sK7) ),
    inference(cnf_transformation,[],[f43])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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

fof(f16,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,k1_lattices(X0,X1,sK6(X0))) != X1
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),X2)) != sK5(X0)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),sK6(X0))) != sK5(X0)
            & m1_subset_1(sK6(X0),u1_struct_0(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f35,f37,f36])).

fof(f55,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    v9_lattices(sK7) ),
    inference(cnf_transformation,[],[f43])).

fof(f61,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f70,plain,(
    r1_lattices(sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

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

fof(f51,plain,(
    ! [X4,X0,X3] :
      ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,(
    v8_lattices(sK7) ),
    inference(cnf_transformation,[],[f43])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k1_lattices(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    ~ r1_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1098,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1242,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1098])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1097,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1243,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1097])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1096,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1244,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1096])).

cnf(c_17,plain,
    ( ~ l3_lattices(X0)
    | l1_lattices(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v7_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,k2_lattices(X1,X3,X2),X0) = k2_lattices(X1,X3,k2_lattices(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_468,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X4)
    | ~ v7_lattices(X1)
    | v2_struct_0(X1)
    | X1 != X4
    | k2_lattices(X1,X3,k2_lattices(X1,X2,X0)) = k2_lattices(X1,k2_lattices(X1,X3,X2),X0) ),
    inference(resolution_lifted,[status(thm)],[c_17,c_6])).

cnf(c_469,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v7_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X3,k2_lattices(X1,X2,X0)) = k2_lattices(X1,k2_lattices(X1,X3,X2),X0) ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_941,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v7_lattices(X1)
    | k2_lattices(X1,X3,k2_lattices(X1,X2,X0)) = k2_lattices(X1,k2_lattices(X1,X3,X2),X0)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_469,c_27])).

cnf(c_942,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | ~ v7_lattices(sK7)
    | k2_lattices(sK7,X2,k2_lattices(sK7,X0,X1)) = k2_lattices(sK7,k2_lattices(sK7,X2,X0),X1) ),
    inference(unflattening,[status(thm)],[c_941])).

cnf(c_23,negated_conjecture,
    ( l3_lattices(sK7) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_26,negated_conjecture,
    ( v7_lattices(sK7) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_865,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X3,k2_lattices(X1,X2,X0)) = k2_lattices(X1,k2_lattices(X1,X3,X2),X0)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_469,c_26])).

cnf(c_866,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k2_lattices(sK7,X2,k2_lattices(sK7,X0,X1)) = k2_lattices(sK7,k2_lattices(sK7,X2,X0),X1) ),
    inference(unflattening,[status(thm)],[c_865])).

cnf(c_944,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | k2_lattices(sK7,X2,k2_lattices(sK7,X0,X1)) = k2_lattices(sK7,k2_lattices(sK7,X2,X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_942,c_27,c_23,c_866])).

cnf(c_945,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | k2_lattices(sK7,X0,k2_lattices(sK7,X1,X2)) = k2_lattices(sK7,k2_lattices(sK7,X0,X1),X2) ),
    inference(renaming,[status(thm)],[c_944])).

cnf(c_1091,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK7))
    | ~ m1_subset_1(X2_51,u1_struct_0(sK7))
    | k2_lattices(sK7,X0_51,k2_lattices(sK7,X1_51,X2_51)) = k2_lattices(sK7,k2_lattices(sK7,X0_51,X1_51),X2_51) ),
    inference(subtyping,[status(esa)],[c_945])).

cnf(c_1248,plain,
    ( k2_lattices(sK7,X0_51,k2_lattices(sK7,X1_51,X2_51)) = k2_lattices(sK7,k2_lattices(sK7,X0_51,X1_51),X2_51)
    | m1_subset_1(X0_51,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X2_51,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1091])).

cnf(c_1880,plain,
    ( k2_lattices(sK7,k2_lattices(sK7,sK8,X0_51),X1_51) = k2_lattices(sK7,sK8,k2_lattices(sK7,X0_51,X1_51))
    | m1_subset_1(X0_51,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_1248])).

cnf(c_3046,plain,
    ( k2_lattices(sK7,sK8,k2_lattices(sK7,sK9,X0_51)) = k2_lattices(sK7,k2_lattices(sK7,sK8,sK9),X0_51)
    | m1_subset_1(X0_51,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1243,c_1880])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_982,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_27])).

cnf(c_983,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ v9_lattices(sK7)
    | ~ l3_lattices(sK7)
    | k2_lattices(sK7,X0,k1_lattices(sK7,X0,X1)) = X0 ),
    inference(unflattening,[status(thm)],[c_982])).

cnf(c_24,negated_conjecture,
    ( v9_lattices(sK7) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_715,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_716,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k2_lattices(sK7,X0,k1_lattices(sK7,X0,X1)) = X0 ),
    inference(unflattening,[status(thm)],[c_715])).

cnf(c_720,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | k2_lattices(sK7,X0,k1_lattices(sK7,X0,X1)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_716,c_27,c_23])).

cnf(c_985,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | k2_lattices(sK7,X0,k1_lattices(sK7,X0,X1)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_983,c_27,c_23,c_716])).

cnf(c_1092,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK7))
    | k2_lattices(sK7,X0_51,k1_lattices(sK7,X0_51,X1_51)) = X0_51 ),
    inference(subtyping,[status(esa)],[c_985])).

cnf(c_1247,plain,
    ( k2_lattices(sK7,X0_51,k1_lattices(sK7,X0_51,X1_51)) = X0_51
    | m1_subset_1(X0_51,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1092])).

cnf(c_1768,plain,
    ( k2_lattices(sK7,sK8,k1_lattices(sK7,sK8,X0_51)) = sK8
    | m1_subset_1(X0_51,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_1247])).

cnf(c_2170,plain,
    ( k2_lattices(sK7,sK8,k1_lattices(sK7,sK8,sK9)) = sK8 ),
    inference(superposition,[status(thm)],[c_1243,c_1768])).

cnf(c_16,plain,
    ( ~ l3_lattices(X0)
    | l2_lattices(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l2_lattices(X0)
    | k1_lattices(X0,X1,X2) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_283,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) = X2 ),
    inference(resolution,[status(thm)],[c_16,c_1])).

cnf(c_19,negated_conjecture,
    ( r1_lattices(sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_361,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X0) = X0
    | sK9 != X0
    | sK8 != X2
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_283,c_19])).

cnf(c_362,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k1_lattices(sK7,sK8,sK9) = sK9 ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_364,plain,
    ( k1_lattices(sK7,sK8,sK9) = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_362,c_27,c_23,c_22,c_21])).

cnf(c_1094,plain,
    ( k1_lattices(sK7,sK8,sK9) = sK9 ),
    inference(subtyping,[status(esa)],[c_364])).

cnf(c_2172,plain,
    ( k2_lattices(sK7,sK8,sK9) = sK8 ),
    inference(light_normalisation,[status(thm)],[c_2170,c_1094])).

cnf(c_3049,plain,
    ( k2_lattices(sK7,sK8,k2_lattices(sK7,sK9,X0_51)) = k2_lattices(sK7,sK8,X0_51)
    | m1_subset_1(X0_51,u1_struct_0(sK7)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3046,c_2172])).

cnf(c_30022,plain,
    ( k2_lattices(sK7,sK8,k2_lattices(sK7,sK9,sK10)) = k2_lattices(sK7,sK8,sK10) ),
    inference(superposition,[status(thm)],[c_1242,c_3049])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_447,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_15])).

cnf(c_448,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_447])).

cnf(c_961,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_448,c_27])).

cnf(c_962,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(k2_lattices(sK7,X0,X1),u1_struct_0(sK7))
    | ~ l3_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_961])).

cnf(c_966,plain,
    ( m1_subset_1(k2_lattices(sK7,X0,X1),u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_962,c_23])).

cnf(c_967,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(k2_lattices(sK7,X0,X1),u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_966])).

cnf(c_1090,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK7))
    | m1_subset_1(k2_lattices(sK7,X0_51,X1_51),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_967])).

cnf(c_1249,plain,
    ( m1_subset_1(X0_51,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k2_lattices(sK7,X0_51,X1_51),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1090])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v8_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_999,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v8_lattices(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_27])).

cnf(c_1000,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | ~ v8_lattices(sK7)
    | k1_lattices(sK7,k2_lattices(sK7,X0,X1),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_999])).

cnf(c_25,negated_conjecture,
    ( v8_lattices(sK7) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_601,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_25])).

cnf(c_602,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k1_lattices(sK7,k2_lattices(sK7,X0,X1),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_601])).

cnf(c_606,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | k1_lattices(sK7,k2_lattices(sK7,X0,X1),X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_602,c_27,c_23])).

cnf(c_1002,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | k1_lattices(sK7,k2_lattices(sK7,X0,X1),X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1000,c_27,c_23,c_602])).

cnf(c_1093,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK7))
    | k1_lattices(sK7,k2_lattices(sK7,X0_51,X1_51),X1_51) = X1_51 ),
    inference(subtyping,[status(esa)],[c_1002])).

cnf(c_1246,plain,
    ( k1_lattices(sK7,k2_lattices(sK7,X0_51,X1_51),X1_51) = X1_51
    | m1_subset_1(X0_51,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1093])).

cnf(c_1339,plain,
    ( k1_lattices(sK7,k2_lattices(sK7,sK8,X0_51),X0_51) = X0_51
    | m1_subset_1(X0_51,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_1246])).

cnf(c_2367,plain,
    ( k1_lattices(sK7,k2_lattices(sK7,sK8,k2_lattices(sK7,X0_51,X1_51)),k2_lattices(sK7,X0_51,X1_51)) = k2_lattices(sK7,X0_51,X1_51)
    | m1_subset_1(X0_51,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1249,c_1339])).

cnf(c_8870,plain,
    ( k1_lattices(sK7,k2_lattices(sK7,sK8,k2_lattices(sK7,sK9,X0_51)),k2_lattices(sK7,sK9,X0_51)) = k2_lattices(sK7,sK9,X0_51)
    | m1_subset_1(X0_51,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1243,c_2367])).

cnf(c_9928,plain,
    ( k1_lattices(sK7,k2_lattices(sK7,sK8,k2_lattices(sK7,sK9,sK10)),k2_lattices(sK7,sK9,sK10)) = k2_lattices(sK7,sK9,sK10) ),
    inference(superposition,[status(thm)],[c_1242,c_8870])).

cnf(c_30233,plain,
    ( k1_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10)) = k2_lattices(sK7,sK9,sK10) ),
    inference(demodulation,[status(thm)],[c_30022,c_9928])).

cnf(c_1277,plain,
    ( m1_subset_1(k2_lattices(sK7,sK8,sK10),u1_struct_0(sK7))
    | ~ m1_subset_1(sK10,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_1090])).

cnf(c_1271,plain,
    ( m1_subset_1(k2_lattices(sK7,sK9,sK10),u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK10,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_1090])).

cnf(c_0,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l2_lattices(X0)
    | k1_lattices(X0,X1,X2) != X2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_306,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) != X2 ),
    inference(resolution,[status(thm)],[c_16,c_0])).

cnf(c_18,negated_conjecture,
    ( ~ r1_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_344,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(sK7,sK9,sK10) != X0
    | k2_lattices(sK7,sK8,sK10) != X2
    | k1_lattices(X1,X2,X0) != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_306,c_18])).

cnf(c_345,plain,
    ( ~ m1_subset_1(k2_lattices(sK7,sK9,sK10),u1_struct_0(sK7))
    | ~ m1_subset_1(k2_lattices(sK7,sK8,sK10),u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k1_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10)) != k2_lattices(sK7,sK9,sK10) ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_347,plain,
    ( ~ m1_subset_1(k2_lattices(sK7,sK9,sK10),u1_struct_0(sK7))
    | ~ m1_subset_1(k2_lattices(sK7,sK8,sK10),u1_struct_0(sK7))
    | k1_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10)) != k2_lattices(sK7,sK9,sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_345,c_27,c_23])).

cnf(c_1095,plain,
    ( ~ m1_subset_1(k2_lattices(sK7,sK9,sK10),u1_struct_0(sK7))
    | ~ m1_subset_1(k2_lattices(sK7,sK8,sK10),u1_struct_0(sK7))
    | k1_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10)) != k2_lattices(sK7,sK9,sK10) ),
    inference(subtyping,[status(esa)],[c_347])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30233,c_1277,c_1271,c_1095,c_20,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:51:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.38/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.38/2.00  
% 11.38/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.38/2.00  
% 11.38/2.00  ------  iProver source info
% 11.38/2.00  
% 11.38/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.38/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.38/2.00  git: non_committed_changes: false
% 11.38/2.00  git: last_make_outside_of_git: false
% 11.38/2.00  
% 11.38/2.00  ------ 
% 11.38/2.00  
% 11.38/2.00  ------ Input Options
% 11.38/2.00  
% 11.38/2.00  --out_options                           all
% 11.38/2.00  --tptp_safe_out                         true
% 11.38/2.00  --problem_path                          ""
% 11.38/2.00  --include_path                          ""
% 11.38/2.00  --clausifier                            res/vclausify_rel
% 11.38/2.00  --clausifier_options                    ""
% 11.38/2.00  --stdin                                 false
% 11.38/2.00  --stats_out                             all
% 11.38/2.00  
% 11.38/2.00  ------ General Options
% 11.38/2.00  
% 11.38/2.00  --fof                                   false
% 11.38/2.00  --time_out_real                         305.
% 11.38/2.00  --time_out_virtual                      -1.
% 11.38/2.00  --symbol_type_check                     false
% 11.38/2.00  --clausify_out                          false
% 11.38/2.00  --sig_cnt_out                           false
% 11.38/2.00  --trig_cnt_out                          false
% 11.38/2.00  --trig_cnt_out_tolerance                1.
% 11.38/2.00  --trig_cnt_out_sk_spl                   false
% 11.38/2.00  --abstr_cl_out                          false
% 11.38/2.00  
% 11.38/2.00  ------ Global Options
% 11.38/2.00  
% 11.38/2.00  --schedule                              default
% 11.38/2.00  --add_important_lit                     false
% 11.38/2.00  --prop_solver_per_cl                    1000
% 11.38/2.00  --min_unsat_core                        false
% 11.38/2.00  --soft_assumptions                      false
% 11.38/2.00  --soft_lemma_size                       3
% 11.38/2.00  --prop_impl_unit_size                   0
% 11.38/2.00  --prop_impl_unit                        []
% 11.38/2.00  --share_sel_clauses                     true
% 11.38/2.00  --reset_solvers                         false
% 11.38/2.00  --bc_imp_inh                            [conj_cone]
% 11.38/2.00  --conj_cone_tolerance                   3.
% 11.38/2.00  --extra_neg_conj                        none
% 11.38/2.00  --large_theory_mode                     true
% 11.38/2.00  --prolific_symb_bound                   200
% 11.38/2.00  --lt_threshold                          2000
% 11.38/2.00  --clause_weak_htbl                      true
% 11.38/2.00  --gc_record_bc_elim                     false
% 11.38/2.00  
% 11.38/2.00  ------ Preprocessing Options
% 11.38/2.00  
% 11.38/2.00  --preprocessing_flag                    true
% 11.38/2.00  --time_out_prep_mult                    0.1
% 11.38/2.00  --splitting_mode                        input
% 11.38/2.00  --splitting_grd                         true
% 11.38/2.00  --splitting_cvd                         false
% 11.38/2.00  --splitting_cvd_svl                     false
% 11.38/2.00  --splitting_nvd                         32
% 11.38/2.00  --sub_typing                            true
% 11.38/2.00  --prep_gs_sim                           true
% 11.38/2.00  --prep_unflatten                        true
% 11.38/2.00  --prep_res_sim                          true
% 11.38/2.00  --prep_upred                            true
% 11.38/2.00  --prep_sem_filter                       exhaustive
% 11.38/2.00  --prep_sem_filter_out                   false
% 11.38/2.00  --pred_elim                             true
% 11.38/2.00  --res_sim_input                         true
% 11.38/2.00  --eq_ax_congr_red                       true
% 11.38/2.00  --pure_diseq_elim                       true
% 11.38/2.00  --brand_transform                       false
% 11.38/2.00  --non_eq_to_eq                          false
% 11.38/2.00  --prep_def_merge                        true
% 11.38/2.00  --prep_def_merge_prop_impl              false
% 11.38/2.00  --prep_def_merge_mbd                    true
% 11.38/2.00  --prep_def_merge_tr_red                 false
% 11.38/2.00  --prep_def_merge_tr_cl                  false
% 11.38/2.00  --smt_preprocessing                     true
% 11.38/2.00  --smt_ac_axioms                         fast
% 11.38/2.00  --preprocessed_out                      false
% 11.38/2.00  --preprocessed_stats                    false
% 11.38/2.00  
% 11.38/2.00  ------ Abstraction refinement Options
% 11.38/2.00  
% 11.38/2.00  --abstr_ref                             []
% 11.38/2.00  --abstr_ref_prep                        false
% 11.38/2.00  --abstr_ref_until_sat                   false
% 11.38/2.00  --abstr_ref_sig_restrict                funpre
% 11.38/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.38/2.00  --abstr_ref_under                       []
% 11.38/2.00  
% 11.38/2.00  ------ SAT Options
% 11.38/2.00  
% 11.38/2.00  --sat_mode                              false
% 11.38/2.00  --sat_fm_restart_options                ""
% 11.38/2.00  --sat_gr_def                            false
% 11.38/2.00  --sat_epr_types                         true
% 11.38/2.00  --sat_non_cyclic_types                  false
% 11.38/2.00  --sat_finite_models                     false
% 11.38/2.00  --sat_fm_lemmas                         false
% 11.38/2.00  --sat_fm_prep                           false
% 11.38/2.00  --sat_fm_uc_incr                        true
% 11.38/2.00  --sat_out_model                         small
% 11.38/2.00  --sat_out_clauses                       false
% 11.38/2.00  
% 11.38/2.00  ------ QBF Options
% 11.38/2.00  
% 11.38/2.00  --qbf_mode                              false
% 11.38/2.00  --qbf_elim_univ                         false
% 11.38/2.00  --qbf_dom_inst                          none
% 11.38/2.00  --qbf_dom_pre_inst                      false
% 11.38/2.00  --qbf_sk_in                             false
% 11.38/2.00  --qbf_pred_elim                         true
% 11.38/2.00  --qbf_split                             512
% 11.38/2.00  
% 11.38/2.00  ------ BMC1 Options
% 11.38/2.00  
% 11.38/2.00  --bmc1_incremental                      false
% 11.38/2.00  --bmc1_axioms                           reachable_all
% 11.38/2.00  --bmc1_min_bound                        0
% 11.38/2.00  --bmc1_max_bound                        -1
% 11.38/2.00  --bmc1_max_bound_default                -1
% 11.38/2.00  --bmc1_symbol_reachability              true
% 11.38/2.00  --bmc1_property_lemmas                  false
% 11.38/2.00  --bmc1_k_induction                      false
% 11.38/2.00  --bmc1_non_equiv_states                 false
% 11.38/2.00  --bmc1_deadlock                         false
% 11.38/2.00  --bmc1_ucm                              false
% 11.38/2.00  --bmc1_add_unsat_core                   none
% 11.38/2.00  --bmc1_unsat_core_children              false
% 11.38/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.38/2.00  --bmc1_out_stat                         full
% 11.38/2.00  --bmc1_ground_init                      false
% 11.38/2.00  --bmc1_pre_inst_next_state              false
% 11.38/2.00  --bmc1_pre_inst_state                   false
% 11.38/2.00  --bmc1_pre_inst_reach_state             false
% 11.38/2.00  --bmc1_out_unsat_core                   false
% 11.38/2.00  --bmc1_aig_witness_out                  false
% 11.38/2.00  --bmc1_verbose                          false
% 11.38/2.00  --bmc1_dump_clauses_tptp                false
% 11.38/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.38/2.00  --bmc1_dump_file                        -
% 11.38/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.38/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.38/2.00  --bmc1_ucm_extend_mode                  1
% 11.38/2.00  --bmc1_ucm_init_mode                    2
% 11.38/2.00  --bmc1_ucm_cone_mode                    none
% 11.38/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.38/2.00  --bmc1_ucm_relax_model                  4
% 11.38/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.38/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.38/2.00  --bmc1_ucm_layered_model                none
% 11.38/2.00  --bmc1_ucm_max_lemma_size               10
% 11.38/2.00  
% 11.38/2.00  ------ AIG Options
% 11.38/2.00  
% 11.38/2.00  --aig_mode                              false
% 11.38/2.00  
% 11.38/2.00  ------ Instantiation Options
% 11.38/2.00  
% 11.38/2.00  --instantiation_flag                    true
% 11.38/2.00  --inst_sos_flag                         true
% 11.38/2.00  --inst_sos_phase                        true
% 11.38/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.38/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.38/2.00  --inst_lit_sel_side                     num_symb
% 11.38/2.00  --inst_solver_per_active                1400
% 11.38/2.00  --inst_solver_calls_frac                1.
% 11.38/2.00  --inst_passive_queue_type               priority_queues
% 11.38/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.38/2.00  --inst_passive_queues_freq              [25;2]
% 11.38/2.00  --inst_dismatching                      true
% 11.38/2.00  --inst_eager_unprocessed_to_passive     true
% 11.38/2.00  --inst_prop_sim_given                   true
% 11.38/2.00  --inst_prop_sim_new                     false
% 11.38/2.00  --inst_subs_new                         false
% 11.38/2.00  --inst_eq_res_simp                      false
% 11.38/2.00  --inst_subs_given                       false
% 11.38/2.00  --inst_orphan_elimination               true
% 11.38/2.00  --inst_learning_loop_flag               true
% 11.38/2.00  --inst_learning_start                   3000
% 11.38/2.00  --inst_learning_factor                  2
% 11.38/2.00  --inst_start_prop_sim_after_learn       3
% 11.38/2.00  --inst_sel_renew                        solver
% 11.38/2.00  --inst_lit_activity_flag                true
% 11.38/2.00  --inst_restr_to_given                   false
% 11.38/2.00  --inst_activity_threshold               500
% 11.38/2.00  --inst_out_proof                        true
% 11.38/2.00  
% 11.38/2.00  ------ Resolution Options
% 11.38/2.00  
% 11.38/2.00  --resolution_flag                       true
% 11.38/2.00  --res_lit_sel                           adaptive
% 11.38/2.00  --res_lit_sel_side                      none
% 11.38/2.00  --res_ordering                          kbo
% 11.38/2.00  --res_to_prop_solver                    active
% 11.38/2.00  --res_prop_simpl_new                    false
% 11.38/2.00  --res_prop_simpl_given                  true
% 11.38/2.00  --res_passive_queue_type                priority_queues
% 11.38/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.38/2.00  --res_passive_queues_freq               [15;5]
% 11.38/2.00  --res_forward_subs                      full
% 11.38/2.00  --res_backward_subs                     full
% 11.38/2.00  --res_forward_subs_resolution           true
% 11.38/2.00  --res_backward_subs_resolution          true
% 11.38/2.00  --res_orphan_elimination                true
% 11.38/2.00  --res_time_limit                        2.
% 11.38/2.00  --res_out_proof                         true
% 11.38/2.00  
% 11.38/2.00  ------ Superposition Options
% 11.38/2.00  
% 11.38/2.00  --superposition_flag                    true
% 11.38/2.00  --sup_passive_queue_type                priority_queues
% 11.38/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.38/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.38/2.00  --demod_completeness_check              fast
% 11.38/2.00  --demod_use_ground                      true
% 11.38/2.00  --sup_to_prop_solver                    passive
% 11.38/2.00  --sup_prop_simpl_new                    true
% 11.38/2.00  --sup_prop_simpl_given                  true
% 11.38/2.00  --sup_fun_splitting                     true
% 11.38/2.00  --sup_smt_interval                      50000
% 11.38/2.00  
% 11.38/2.00  ------ Superposition Simplification Setup
% 11.38/2.00  
% 11.38/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.38/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.38/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.38/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.38/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.38/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.38/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.38/2.00  --sup_immed_triv                        [TrivRules]
% 11.38/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.38/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.38/2.00  --sup_immed_bw_main                     []
% 11.38/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.38/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.38/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.38/2.00  --sup_input_bw                          []
% 11.38/2.00  
% 11.38/2.00  ------ Combination Options
% 11.38/2.00  
% 11.38/2.00  --comb_res_mult                         3
% 11.38/2.00  --comb_sup_mult                         2
% 11.38/2.00  --comb_inst_mult                        10
% 11.38/2.00  
% 11.38/2.00  ------ Debug Options
% 11.38/2.00  
% 11.38/2.00  --dbg_backtrace                         false
% 11.38/2.00  --dbg_dump_prop_clauses                 false
% 11.38/2.00  --dbg_dump_prop_clauses_file            -
% 11.38/2.00  --dbg_out_stat                          false
% 11.38/2.00  ------ Parsing...
% 11.38/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.38/2.00  
% 11.38/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 11.38/2.00  
% 11.38/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.38/2.00  
% 11.38/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.38/2.00  ------ Proving...
% 11.38/2.00  ------ Problem Properties 
% 11.38/2.00  
% 11.38/2.00  
% 11.38/2.00  clauses                                 10
% 11.38/2.00  conjectures                             3
% 11.38/2.00  EPR                                     0
% 11.38/2.00  Horn                                    10
% 11.38/2.00  unary                                   4
% 11.38/2.00  binary                                  1
% 11.38/2.00  lits                                    22
% 11.38/2.00  lits eq                                 7
% 11.38/2.00  fd_pure                                 0
% 11.38/2.00  fd_pseudo                               0
% 11.38/2.00  fd_cond                                 0
% 11.38/2.00  fd_pseudo_cond                          0
% 11.38/2.00  AC symbols                              0
% 11.38/2.00  
% 11.38/2.00  ------ Schedule dynamic 5 is on 
% 11.38/2.00  
% 11.38/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.38/2.00  
% 11.38/2.00  
% 11.38/2.00  ------ 
% 11.38/2.00  Current options:
% 11.38/2.00  ------ 
% 11.38/2.00  
% 11.38/2.00  ------ Input Options
% 11.38/2.00  
% 11.38/2.00  --out_options                           all
% 11.38/2.00  --tptp_safe_out                         true
% 11.38/2.00  --problem_path                          ""
% 11.38/2.00  --include_path                          ""
% 11.38/2.00  --clausifier                            res/vclausify_rel
% 11.38/2.00  --clausifier_options                    ""
% 11.38/2.00  --stdin                                 false
% 11.38/2.00  --stats_out                             all
% 11.38/2.00  
% 11.38/2.00  ------ General Options
% 11.38/2.00  
% 11.38/2.00  --fof                                   false
% 11.38/2.00  --time_out_real                         305.
% 11.38/2.00  --time_out_virtual                      -1.
% 11.38/2.00  --symbol_type_check                     false
% 11.38/2.00  --clausify_out                          false
% 11.38/2.00  --sig_cnt_out                           false
% 11.38/2.00  --trig_cnt_out                          false
% 11.38/2.00  --trig_cnt_out_tolerance                1.
% 11.38/2.00  --trig_cnt_out_sk_spl                   false
% 11.38/2.00  --abstr_cl_out                          false
% 11.38/2.00  
% 11.38/2.00  ------ Global Options
% 11.38/2.00  
% 11.38/2.00  --schedule                              default
% 11.38/2.00  --add_important_lit                     false
% 11.38/2.00  --prop_solver_per_cl                    1000
% 11.38/2.00  --min_unsat_core                        false
% 11.38/2.00  --soft_assumptions                      false
% 11.38/2.00  --soft_lemma_size                       3
% 11.38/2.00  --prop_impl_unit_size                   0
% 11.38/2.00  --prop_impl_unit                        []
% 11.38/2.00  --share_sel_clauses                     true
% 11.38/2.00  --reset_solvers                         false
% 11.38/2.00  --bc_imp_inh                            [conj_cone]
% 11.38/2.00  --conj_cone_tolerance                   3.
% 11.38/2.00  --extra_neg_conj                        none
% 11.38/2.00  --large_theory_mode                     true
% 11.38/2.00  --prolific_symb_bound                   200
% 11.38/2.00  --lt_threshold                          2000
% 11.38/2.00  --clause_weak_htbl                      true
% 11.38/2.00  --gc_record_bc_elim                     false
% 11.38/2.00  
% 11.38/2.00  ------ Preprocessing Options
% 11.38/2.00  
% 11.38/2.00  --preprocessing_flag                    true
% 11.38/2.00  --time_out_prep_mult                    0.1
% 11.38/2.00  --splitting_mode                        input
% 11.38/2.00  --splitting_grd                         true
% 11.38/2.00  --splitting_cvd                         false
% 11.38/2.00  --splitting_cvd_svl                     false
% 11.38/2.00  --splitting_nvd                         32
% 11.38/2.00  --sub_typing                            true
% 11.38/2.00  --prep_gs_sim                           true
% 11.38/2.00  --prep_unflatten                        true
% 11.38/2.00  --prep_res_sim                          true
% 11.38/2.00  --prep_upred                            true
% 11.38/2.00  --prep_sem_filter                       exhaustive
% 11.38/2.00  --prep_sem_filter_out                   false
% 11.38/2.00  --pred_elim                             true
% 11.38/2.00  --res_sim_input                         true
% 11.38/2.00  --eq_ax_congr_red                       true
% 11.38/2.00  --pure_diseq_elim                       true
% 11.38/2.00  --brand_transform                       false
% 11.38/2.00  --non_eq_to_eq                          false
% 11.38/2.00  --prep_def_merge                        true
% 11.38/2.00  --prep_def_merge_prop_impl              false
% 11.38/2.00  --prep_def_merge_mbd                    true
% 11.38/2.00  --prep_def_merge_tr_red                 false
% 11.38/2.00  --prep_def_merge_tr_cl                  false
% 11.38/2.00  --smt_preprocessing                     true
% 11.38/2.00  --smt_ac_axioms                         fast
% 11.38/2.00  --preprocessed_out                      false
% 11.38/2.00  --preprocessed_stats                    false
% 11.38/2.00  
% 11.38/2.00  ------ Abstraction refinement Options
% 11.38/2.00  
% 11.38/2.00  --abstr_ref                             []
% 11.38/2.00  --abstr_ref_prep                        false
% 11.38/2.00  --abstr_ref_until_sat                   false
% 11.38/2.00  --abstr_ref_sig_restrict                funpre
% 11.38/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.38/2.00  --abstr_ref_under                       []
% 11.38/2.00  
% 11.38/2.00  ------ SAT Options
% 11.38/2.00  
% 11.38/2.00  --sat_mode                              false
% 11.38/2.00  --sat_fm_restart_options                ""
% 11.38/2.00  --sat_gr_def                            false
% 11.38/2.00  --sat_epr_types                         true
% 11.38/2.00  --sat_non_cyclic_types                  false
% 11.38/2.00  --sat_finite_models                     false
% 11.38/2.00  --sat_fm_lemmas                         false
% 11.38/2.00  --sat_fm_prep                           false
% 11.38/2.00  --sat_fm_uc_incr                        true
% 11.38/2.00  --sat_out_model                         small
% 11.38/2.00  --sat_out_clauses                       false
% 11.38/2.00  
% 11.38/2.00  ------ QBF Options
% 11.38/2.00  
% 11.38/2.00  --qbf_mode                              false
% 11.38/2.00  --qbf_elim_univ                         false
% 11.38/2.00  --qbf_dom_inst                          none
% 11.38/2.00  --qbf_dom_pre_inst                      false
% 11.38/2.00  --qbf_sk_in                             false
% 11.38/2.00  --qbf_pred_elim                         true
% 11.38/2.00  --qbf_split                             512
% 11.38/2.00  
% 11.38/2.00  ------ BMC1 Options
% 11.38/2.00  
% 11.38/2.00  --bmc1_incremental                      false
% 11.38/2.00  --bmc1_axioms                           reachable_all
% 11.38/2.00  --bmc1_min_bound                        0
% 11.38/2.00  --bmc1_max_bound                        -1
% 11.38/2.00  --bmc1_max_bound_default                -1
% 11.38/2.00  --bmc1_symbol_reachability              true
% 11.38/2.00  --bmc1_property_lemmas                  false
% 11.38/2.00  --bmc1_k_induction                      false
% 11.38/2.00  --bmc1_non_equiv_states                 false
% 11.38/2.00  --bmc1_deadlock                         false
% 11.38/2.00  --bmc1_ucm                              false
% 11.38/2.00  --bmc1_add_unsat_core                   none
% 11.38/2.00  --bmc1_unsat_core_children              false
% 11.38/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.38/2.00  --bmc1_out_stat                         full
% 11.38/2.00  --bmc1_ground_init                      false
% 11.38/2.00  --bmc1_pre_inst_next_state              false
% 11.38/2.00  --bmc1_pre_inst_state                   false
% 11.38/2.00  --bmc1_pre_inst_reach_state             false
% 11.38/2.00  --bmc1_out_unsat_core                   false
% 11.38/2.00  --bmc1_aig_witness_out                  false
% 11.38/2.00  --bmc1_verbose                          false
% 11.38/2.00  --bmc1_dump_clauses_tptp                false
% 11.38/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.38/2.00  --bmc1_dump_file                        -
% 11.38/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.38/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.38/2.00  --bmc1_ucm_extend_mode                  1
% 11.38/2.00  --bmc1_ucm_init_mode                    2
% 11.38/2.00  --bmc1_ucm_cone_mode                    none
% 11.38/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.38/2.00  --bmc1_ucm_relax_model                  4
% 11.38/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.38/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.38/2.00  --bmc1_ucm_layered_model                none
% 11.38/2.00  --bmc1_ucm_max_lemma_size               10
% 11.38/2.00  
% 11.38/2.00  ------ AIG Options
% 11.38/2.00  
% 11.38/2.00  --aig_mode                              false
% 11.38/2.00  
% 11.38/2.00  ------ Instantiation Options
% 11.38/2.00  
% 11.38/2.00  --instantiation_flag                    true
% 11.38/2.00  --inst_sos_flag                         true
% 11.38/2.00  --inst_sos_phase                        true
% 11.38/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.38/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.38/2.00  --inst_lit_sel_side                     none
% 11.38/2.00  --inst_solver_per_active                1400
% 11.38/2.00  --inst_solver_calls_frac                1.
% 11.38/2.00  --inst_passive_queue_type               priority_queues
% 11.38/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.38/2.00  --inst_passive_queues_freq              [25;2]
% 11.38/2.00  --inst_dismatching                      true
% 11.38/2.00  --inst_eager_unprocessed_to_passive     true
% 11.38/2.00  --inst_prop_sim_given                   true
% 11.38/2.00  --inst_prop_sim_new                     false
% 11.38/2.00  --inst_subs_new                         false
% 11.38/2.00  --inst_eq_res_simp                      false
% 11.38/2.00  --inst_subs_given                       false
% 11.38/2.00  --inst_orphan_elimination               true
% 11.38/2.00  --inst_learning_loop_flag               true
% 11.38/2.00  --inst_learning_start                   3000
% 11.38/2.00  --inst_learning_factor                  2
% 11.38/2.00  --inst_start_prop_sim_after_learn       3
% 11.38/2.00  --inst_sel_renew                        solver
% 11.38/2.00  --inst_lit_activity_flag                true
% 11.38/2.00  --inst_restr_to_given                   false
% 11.38/2.00  --inst_activity_threshold               500
% 11.38/2.00  --inst_out_proof                        true
% 11.38/2.00  
% 11.38/2.00  ------ Resolution Options
% 11.38/2.00  
% 11.38/2.00  --resolution_flag                       false
% 11.38/2.00  --res_lit_sel                           adaptive
% 11.38/2.00  --res_lit_sel_side                      none
% 11.38/2.00  --res_ordering                          kbo
% 11.38/2.00  --res_to_prop_solver                    active
% 11.38/2.00  --res_prop_simpl_new                    false
% 11.38/2.00  --res_prop_simpl_given                  true
% 11.38/2.00  --res_passive_queue_type                priority_queues
% 11.38/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.38/2.00  --res_passive_queues_freq               [15;5]
% 11.38/2.00  --res_forward_subs                      full
% 11.38/2.00  --res_backward_subs                     full
% 11.38/2.00  --res_forward_subs_resolution           true
% 11.38/2.00  --res_backward_subs_resolution          true
% 11.38/2.00  --res_orphan_elimination                true
% 11.38/2.00  --res_time_limit                        2.
% 11.38/2.00  --res_out_proof                         true
% 11.38/2.00  
% 11.38/2.00  ------ Superposition Options
% 11.38/2.00  
% 11.38/2.00  --superposition_flag                    true
% 11.38/2.00  --sup_passive_queue_type                priority_queues
% 11.38/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.38/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.38/2.00  --demod_completeness_check              fast
% 11.38/2.00  --demod_use_ground                      true
% 11.38/2.00  --sup_to_prop_solver                    passive
% 11.38/2.00  --sup_prop_simpl_new                    true
% 11.38/2.00  --sup_prop_simpl_given                  true
% 11.38/2.00  --sup_fun_splitting                     true
% 11.38/2.00  --sup_smt_interval                      50000
% 11.38/2.00  
% 11.38/2.00  ------ Superposition Simplification Setup
% 11.38/2.00  
% 11.38/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.38/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.38/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.38/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.38/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.38/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.38/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.38/2.00  --sup_immed_triv                        [TrivRules]
% 11.38/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.38/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.38/2.00  --sup_immed_bw_main                     []
% 11.38/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.38/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.38/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.38/2.00  --sup_input_bw                          []
% 11.38/2.00  
% 11.38/2.00  ------ Combination Options
% 11.38/2.00  
% 11.38/2.00  --comb_res_mult                         3
% 11.38/2.00  --comb_sup_mult                         2
% 11.38/2.00  --comb_inst_mult                        10
% 11.38/2.00  
% 11.38/2.00  ------ Debug Options
% 11.38/2.00  
% 11.38/2.00  --dbg_backtrace                         false
% 11.38/2.00  --dbg_dump_prop_clauses                 false
% 11.38/2.00  --dbg_dump_prop_clauses_file            -
% 11.38/2.00  --dbg_out_stat                          false
% 11.38/2.00  
% 11.38/2.00  
% 11.38/2.00  
% 11.38/2.00  
% 11.38/2.00  ------ Proving...
% 11.38/2.00  
% 11.38/2.00  
% 11.38/2.00  % SZS status Theorem for theBenchmark.p
% 11.38/2.00  
% 11.38/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.38/2.00  
% 11.38/2.00  fof(f7,conjecture,(
% 11.38/2.00    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)))))))),
% 11.38/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.38/2.00  
% 11.38/2.00  fof(f8,negated_conjecture,(
% 11.38/2.00    ~! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)))))))),
% 11.38/2.00    inference(negated_conjecture,[],[f7])).
% 11.38/2.00  
% 11.38/2.00  fof(f20,plain,(
% 11.38/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,X1,X2)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)))),
% 11.38/2.00    inference(ennf_transformation,[],[f8])).
% 11.38/2.00  
% 11.38/2.00  fof(f21,plain,(
% 11.38/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0))),
% 11.38/2.00    inference(flattening,[],[f20])).
% 11.38/2.00  
% 11.38/2.00  fof(f42,plain,(
% 11.38/2.00    ( ! [X2,X0,X1] : (? [X3] : (~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,k2_lattices(X0,X1,sK10),k2_lattices(X0,X2,sK10)) & r1_lattices(X0,X1,X2) & m1_subset_1(sK10,u1_struct_0(X0)))) )),
% 11.38/2.00    introduced(choice_axiom,[])).
% 11.38/2.00  
% 11.38/2.00  fof(f41,plain,(
% 11.38/2.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,sK9,X3)) & r1_lattices(X0,X1,sK9) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK9,u1_struct_0(X0)))) )),
% 11.38/2.00    introduced(choice_axiom,[])).
% 11.38/2.00  
% 11.38/2.00  fof(f40,plain,(
% 11.38/2.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~r1_lattices(X0,k2_lattices(X0,sK8,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,sK8,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK8,u1_struct_0(X0)))) )),
% 11.38/2.00    introduced(choice_axiom,[])).
% 11.38/2.00  
% 11.38/2.00  fof(f39,plain,(
% 11.38/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_lattices(sK7,k2_lattices(sK7,X1,X3),k2_lattices(sK7,X2,X3)) & r1_lattices(sK7,X1,X2) & m1_subset_1(X3,u1_struct_0(sK7))) & m1_subset_1(X2,u1_struct_0(sK7))) & m1_subset_1(X1,u1_struct_0(sK7))) & l3_lattices(sK7) & v9_lattices(sK7) & v8_lattices(sK7) & v7_lattices(sK7) & ~v2_struct_0(sK7))),
% 11.38/2.00    introduced(choice_axiom,[])).
% 11.38/2.00  
% 11.38/2.00  fof(f43,plain,(
% 11.38/2.00    (((~r1_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10)) & r1_lattices(sK7,sK8,sK9) & m1_subset_1(sK10,u1_struct_0(sK7))) & m1_subset_1(sK9,u1_struct_0(sK7))) & m1_subset_1(sK8,u1_struct_0(sK7))) & l3_lattices(sK7) & v9_lattices(sK7) & v8_lattices(sK7) & v7_lattices(sK7) & ~v2_struct_0(sK7)),
% 11.38/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f21,f42,f41,f40,f39])).
% 11.38/2.00  
% 11.38/2.00  fof(f69,plain,(
% 11.38/2.00    m1_subset_1(sK10,u1_struct_0(sK7))),
% 11.38/2.00    inference(cnf_transformation,[],[f43])).
% 11.38/2.00  
% 11.38/2.00  fof(f68,plain,(
% 11.38/2.00    m1_subset_1(sK9,u1_struct_0(sK7))),
% 11.38/2.00    inference(cnf_transformation,[],[f43])).
% 11.38/2.00  
% 11.38/2.00  fof(f67,plain,(
% 11.38/2.00    m1_subset_1(sK8,u1_struct_0(sK7))),
% 11.38/2.00    inference(cnf_transformation,[],[f43])).
% 11.38/2.00  
% 11.38/2.00  fof(f6,axiom,(
% 11.38/2.00    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 11.38/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.38/2.00  
% 11.38/2.00  fof(f19,plain,(
% 11.38/2.00    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 11.38/2.00    inference(ennf_transformation,[],[f6])).
% 11.38/2.00  
% 11.38/2.00  fof(f60,plain,(
% 11.38/2.00    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 11.38/2.00    inference(cnf_transformation,[],[f19])).
% 11.38/2.00  
% 11.38/2.00  fof(f2,axiom,(
% 11.38/2.00    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v7_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3))))))),
% 11.38/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.38/2.00  
% 11.38/2.00  fof(f11,plain,(
% 11.38/2.00    ! [X0] : ((v7_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 11.38/2.00    inference(ennf_transformation,[],[f2])).
% 11.38/2.00  
% 11.38/2.00  fof(f12,plain,(
% 11.38/2.00    ! [X0] : ((v7_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(flattening,[],[f11])).
% 11.38/2.00  
% 11.38/2.00  fof(f23,plain,(
% 11.38/2.00    ! [X0] : (((v7_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v7_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(nnf_transformation,[],[f12])).
% 11.38/2.00  
% 11.38/2.00  fof(f24,plain,(
% 11.38/2.00    ! [X0] : (((v7_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v7_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(rectify,[],[f23])).
% 11.38/2.00  
% 11.38/2.00  fof(f27,plain,(
% 11.38/2.00    ( ! [X2,X1] : (! [X0] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) => (k2_lattices(X0,X1,k2_lattices(X0,X2,sK2(X0))) != k2_lattices(X0,k2_lattices(X0,X1,X2),sK2(X0)) & m1_subset_1(sK2(X0),u1_struct_0(X0))))) )),
% 11.38/2.00    introduced(choice_axiom,[])).
% 11.38/2.00  
% 11.38/2.00  fof(f26,plain,(
% 11.38/2.00    ( ! [X1] : (! [X0] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,sK1(X0),X3)) != k2_lattices(X0,k2_lattices(X0,X1,sK1(X0)),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK1(X0),u1_struct_0(X0))))) )),
% 11.38/2.00    introduced(choice_axiom,[])).
% 11.38/2.00  
% 11.38/2.00  fof(f25,plain,(
% 11.38/2.00    ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k2_lattices(X0,k2_lattices(X0,sK0(X0),X2),X3) != k2_lattices(X0,sK0(X0),k2_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0))))),
% 11.38/2.00    introduced(choice_axiom,[])).
% 11.38/2.00  
% 11.38/2.00  fof(f28,plain,(
% 11.38/2.00    ! [X0] : (((v7_lattices(X0) | (((k2_lattices(X0,k2_lattices(X0,sK0(X0),sK1(X0)),sK2(X0)) != k2_lattices(X0,sK0(X0),k2_lattices(X0,sK1(X0),sK2(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))) & m1_subset_1(sK1(X0),u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v7_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).
% 11.38/2.00  
% 11.38/2.00  fof(f46,plain,(
% 11.38/2.00    ( ! [X6,X4,X0,X5] : (k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v7_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.38/2.00    inference(cnf_transformation,[],[f28])).
% 11.38/2.00  
% 11.38/2.00  fof(f62,plain,(
% 11.38/2.00    ~v2_struct_0(sK7)),
% 11.38/2.00    inference(cnf_transformation,[],[f43])).
% 11.38/2.00  
% 11.38/2.00  fof(f66,plain,(
% 11.38/2.00    l3_lattices(sK7)),
% 11.38/2.00    inference(cnf_transformation,[],[f43])).
% 11.38/2.00  
% 11.38/2.00  fof(f63,plain,(
% 11.38/2.00    v7_lattices(sK7)),
% 11.38/2.00    inference(cnf_transformation,[],[f43])).
% 11.38/2.00  
% 11.38/2.00  fof(f4,axiom,(
% 11.38/2.00    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 11.38/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.38/2.00  
% 11.38/2.00  fof(f15,plain,(
% 11.38/2.00    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 11.38/2.00    inference(ennf_transformation,[],[f4])).
% 11.38/2.00  
% 11.38/2.00  fof(f16,plain,(
% 11.38/2.00    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(flattening,[],[f15])).
% 11.38/2.00  
% 11.38/2.00  fof(f34,plain,(
% 11.38/2.00    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(nnf_transformation,[],[f16])).
% 11.38/2.00  
% 11.38/2.00  fof(f35,plain,(
% 11.38/2.00    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(rectify,[],[f34])).
% 11.38/2.00  
% 11.38/2.00  fof(f37,plain,(
% 11.38/2.00    ( ! [X1] : (! [X0] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,X1,k1_lattices(X0,X1,sK6(X0))) != X1 & m1_subset_1(sK6(X0),u1_struct_0(X0))))) )),
% 11.38/2.00    introduced(choice_axiom,[])).
% 11.38/2.00  
% 11.38/2.00  fof(f36,plain,(
% 11.38/2.00    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),X2)) != sK5(X0) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 11.38/2.00    introduced(choice_axiom,[])).
% 11.38/2.00  
% 11.38/2.00  fof(f38,plain,(
% 11.38/2.00    ! [X0] : (((v9_lattices(X0) | ((k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),sK6(X0))) != sK5(X0) & m1_subset_1(sK6(X0),u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f35,f37,f36])).
% 11.38/2.00  
% 11.38/2.00  fof(f55,plain,(
% 11.38/2.00    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v9_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 11.38/2.00    inference(cnf_transformation,[],[f38])).
% 11.38/2.00  
% 11.38/2.00  fof(f65,plain,(
% 11.38/2.00    v9_lattices(sK7)),
% 11.38/2.00    inference(cnf_transformation,[],[f43])).
% 11.38/2.00  
% 11.38/2.00  fof(f61,plain,(
% 11.38/2.00    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 11.38/2.00    inference(cnf_transformation,[],[f19])).
% 11.38/2.00  
% 11.38/2.00  fof(f1,axiom,(
% 11.38/2.00    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 11.38/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.38/2.00  
% 11.38/2.00  fof(f9,plain,(
% 11.38/2.00    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 11.38/2.00    inference(ennf_transformation,[],[f1])).
% 11.38/2.00  
% 11.38/2.00  fof(f10,plain,(
% 11.38/2.00    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(flattening,[],[f9])).
% 11.38/2.00  
% 11.38/2.00  fof(f22,plain,(
% 11.38/2.00    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(nnf_transformation,[],[f10])).
% 11.38/2.00  
% 11.38/2.00  fof(f44,plain,(
% 11.38/2.00    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 11.38/2.00    inference(cnf_transformation,[],[f22])).
% 11.38/2.00  
% 11.38/2.00  fof(f70,plain,(
% 11.38/2.00    r1_lattices(sK7,sK8,sK9)),
% 11.38/2.00    inference(cnf_transformation,[],[f43])).
% 11.38/2.00  
% 11.38/2.00  fof(f5,axiom,(
% 11.38/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 11.38/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.38/2.00  
% 11.38/2.00  fof(f17,plain,(
% 11.38/2.00    ! [X0,X1,X2] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)))),
% 11.38/2.00    inference(ennf_transformation,[],[f5])).
% 11.38/2.00  
% 11.38/2.00  fof(f18,plain,(
% 11.38/2.00    ! [X0,X1,X2] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(flattening,[],[f17])).
% 11.38/2.00  
% 11.38/2.00  fof(f59,plain,(
% 11.38/2.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.38/2.00    inference(cnf_transformation,[],[f18])).
% 11.38/2.00  
% 11.38/2.00  fof(f3,axiom,(
% 11.38/2.00    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 11.38/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.38/2.00  
% 11.38/2.00  fof(f13,plain,(
% 11.38/2.00    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 11.38/2.00    inference(ennf_transformation,[],[f3])).
% 11.38/2.00  
% 11.38/2.00  fof(f14,plain,(
% 11.38/2.00    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(flattening,[],[f13])).
% 11.38/2.00  
% 11.38/2.00  fof(f29,plain,(
% 11.38/2.00    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(nnf_transformation,[],[f14])).
% 11.38/2.00  
% 11.38/2.00  fof(f30,plain,(
% 11.38/2.00    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(rectify,[],[f29])).
% 11.38/2.00  
% 11.38/2.00  fof(f32,plain,(
% 11.38/2.00    ( ! [X1] : (! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (k1_lattices(X0,k2_lattices(X0,X1,sK4(X0)),sK4(X0)) != sK4(X0) & m1_subset_1(sK4(X0),u1_struct_0(X0))))) )),
% 11.38/2.00    introduced(choice_axiom,[])).
% 11.38/2.00  
% 11.38/2.00  fof(f31,plain,(
% 11.38/2.00    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 11.38/2.00    introduced(choice_axiom,[])).
% 11.38/2.00  
% 11.38/2.00  fof(f33,plain,(
% 11.38/2.00    ! [X0] : (((v8_lattices(X0) | ((k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0)) != sK4(X0) & m1_subset_1(sK4(X0),u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.38/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f30,f32,f31])).
% 11.38/2.00  
% 11.38/2.00  fof(f51,plain,(
% 11.38/2.00    ( ! [X4,X0,X3] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v8_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 11.38/2.00    inference(cnf_transformation,[],[f33])).
% 11.38/2.00  
% 11.38/2.00  fof(f64,plain,(
% 11.38/2.00    v8_lattices(sK7)),
% 11.38/2.00    inference(cnf_transformation,[],[f43])).
% 11.38/2.00  
% 11.38/2.00  fof(f45,plain,(
% 11.38/2.00    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 11.38/2.00    inference(cnf_transformation,[],[f22])).
% 11.38/2.00  
% 11.38/2.00  fof(f71,plain,(
% 11.38/2.00    ~r1_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10))),
% 11.38/2.00    inference(cnf_transformation,[],[f43])).
% 11.38/2.00  
% 11.38/2.00  cnf(c_20,negated_conjecture,
% 11.38/2.00      ( m1_subset_1(sK10,u1_struct_0(sK7)) ),
% 11.38/2.00      inference(cnf_transformation,[],[f69]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1098,negated_conjecture,
% 11.38/2.00      ( m1_subset_1(sK10,u1_struct_0(sK7)) ),
% 11.38/2.00      inference(subtyping,[status(esa)],[c_20]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1242,plain,
% 11.38/2.00      ( m1_subset_1(sK10,u1_struct_0(sK7)) = iProver_top ),
% 11.38/2.00      inference(predicate_to_equality,[status(thm)],[c_1098]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_21,negated_conjecture,
% 11.38/2.00      ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
% 11.38/2.00      inference(cnf_transformation,[],[f68]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1097,negated_conjecture,
% 11.38/2.00      ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
% 11.38/2.00      inference(subtyping,[status(esa)],[c_21]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1243,plain,
% 11.38/2.00      ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
% 11.38/2.00      inference(predicate_to_equality,[status(thm)],[c_1097]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_22,negated_conjecture,
% 11.38/2.00      ( m1_subset_1(sK8,u1_struct_0(sK7)) ),
% 11.38/2.00      inference(cnf_transformation,[],[f67]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1096,negated_conjecture,
% 11.38/2.00      ( m1_subset_1(sK8,u1_struct_0(sK7)) ),
% 11.38/2.00      inference(subtyping,[status(esa)],[c_22]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1244,plain,
% 11.38/2.00      ( m1_subset_1(sK8,u1_struct_0(sK7)) = iProver_top ),
% 11.38/2.00      inference(predicate_to_equality,[status(thm)],[c_1096]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_17,plain,
% 11.38/2.00      ( ~ l3_lattices(X0) | l1_lattices(X0) ),
% 11.38/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_6,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 11.38/2.00      | ~ l1_lattices(X1)
% 11.38/2.00      | ~ v7_lattices(X1)
% 11.38/2.00      | v2_struct_0(X1)
% 11.38/2.00      | k2_lattices(X1,k2_lattices(X1,X3,X2),X0) = k2_lattices(X1,X3,k2_lattices(X1,X2,X0)) ),
% 11.38/2.00      inference(cnf_transformation,[],[f46]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_468,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 11.38/2.00      | ~ l3_lattices(X4)
% 11.38/2.00      | ~ v7_lattices(X1)
% 11.38/2.00      | v2_struct_0(X1)
% 11.38/2.00      | X1 != X4
% 11.38/2.00      | k2_lattices(X1,X3,k2_lattices(X1,X2,X0)) = k2_lattices(X1,k2_lattices(X1,X3,X2),X0) ),
% 11.38/2.00      inference(resolution_lifted,[status(thm)],[c_17,c_6]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_469,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 11.38/2.00      | ~ l3_lattices(X1)
% 11.38/2.00      | ~ v7_lattices(X1)
% 11.38/2.00      | v2_struct_0(X1)
% 11.38/2.00      | k2_lattices(X1,X3,k2_lattices(X1,X2,X0)) = k2_lattices(X1,k2_lattices(X1,X3,X2),X0) ),
% 11.38/2.00      inference(unflattening,[status(thm)],[c_468]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_27,negated_conjecture,
% 11.38/2.00      ( ~ v2_struct_0(sK7) ),
% 11.38/2.00      inference(cnf_transformation,[],[f62]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_941,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 11.38/2.00      | ~ l3_lattices(X1)
% 11.38/2.00      | ~ v7_lattices(X1)
% 11.38/2.00      | k2_lattices(X1,X3,k2_lattices(X1,X2,X0)) = k2_lattices(X1,k2_lattices(X1,X3,X2),X0)
% 11.38/2.00      | sK7 != X1 ),
% 11.38/2.00      inference(resolution_lifted,[status(thm)],[c_469,c_27]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_942,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 11.38/2.00      | ~ l3_lattices(sK7)
% 11.38/2.00      | ~ v7_lattices(sK7)
% 11.38/2.00      | k2_lattices(sK7,X2,k2_lattices(sK7,X0,X1)) = k2_lattices(sK7,k2_lattices(sK7,X2,X0),X1) ),
% 11.38/2.00      inference(unflattening,[status(thm)],[c_941]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_23,negated_conjecture,
% 11.38/2.00      ( l3_lattices(sK7) ),
% 11.38/2.00      inference(cnf_transformation,[],[f66]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_26,negated_conjecture,
% 11.38/2.00      ( v7_lattices(sK7) ),
% 11.38/2.00      inference(cnf_transformation,[],[f63]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_865,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 11.38/2.00      | ~ l3_lattices(X1)
% 11.38/2.00      | v2_struct_0(X1)
% 11.38/2.00      | k2_lattices(X1,X3,k2_lattices(X1,X2,X0)) = k2_lattices(X1,k2_lattices(X1,X3,X2),X0)
% 11.38/2.00      | sK7 != X1 ),
% 11.38/2.00      inference(resolution_lifted,[status(thm)],[c_469,c_26]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_866,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 11.38/2.00      | ~ l3_lattices(sK7)
% 11.38/2.00      | v2_struct_0(sK7)
% 11.38/2.00      | k2_lattices(sK7,X2,k2_lattices(sK7,X0,X1)) = k2_lattices(sK7,k2_lattices(sK7,X2,X0),X1) ),
% 11.38/2.00      inference(unflattening,[status(thm)],[c_865]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_944,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 11.38/2.00      | k2_lattices(sK7,X2,k2_lattices(sK7,X0,X1)) = k2_lattices(sK7,k2_lattices(sK7,X2,X0),X1) ),
% 11.38/2.00      inference(global_propositional_subsumption,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_942,c_27,c_23,c_866]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_945,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 11.38/2.00      | k2_lattices(sK7,X0,k2_lattices(sK7,X1,X2)) = k2_lattices(sK7,k2_lattices(sK7,X0,X1),X2) ),
% 11.38/2.00      inference(renaming,[status(thm)],[c_944]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1091,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0_51,u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(X1_51,u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(X2_51,u1_struct_0(sK7))
% 11.38/2.00      | k2_lattices(sK7,X0_51,k2_lattices(sK7,X1_51,X2_51)) = k2_lattices(sK7,k2_lattices(sK7,X0_51,X1_51),X2_51) ),
% 11.38/2.00      inference(subtyping,[status(esa)],[c_945]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1248,plain,
% 11.38/2.00      ( k2_lattices(sK7,X0_51,k2_lattices(sK7,X1_51,X2_51)) = k2_lattices(sK7,k2_lattices(sK7,X0_51,X1_51),X2_51)
% 11.38/2.00      | m1_subset_1(X0_51,u1_struct_0(sK7)) != iProver_top
% 11.38/2.00      | m1_subset_1(X1_51,u1_struct_0(sK7)) != iProver_top
% 11.38/2.00      | m1_subset_1(X2_51,u1_struct_0(sK7)) != iProver_top ),
% 11.38/2.00      inference(predicate_to_equality,[status(thm)],[c_1091]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1880,plain,
% 11.38/2.00      ( k2_lattices(sK7,k2_lattices(sK7,sK8,X0_51),X1_51) = k2_lattices(sK7,sK8,k2_lattices(sK7,X0_51,X1_51))
% 11.38/2.00      | m1_subset_1(X0_51,u1_struct_0(sK7)) != iProver_top
% 11.38/2.00      | m1_subset_1(X1_51,u1_struct_0(sK7)) != iProver_top ),
% 11.38/2.00      inference(superposition,[status(thm)],[c_1244,c_1248]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_3046,plain,
% 11.38/2.00      ( k2_lattices(sK7,sK8,k2_lattices(sK7,sK9,X0_51)) = k2_lattices(sK7,k2_lattices(sK7,sK8,sK9),X0_51)
% 11.38/2.00      | m1_subset_1(X0_51,u1_struct_0(sK7)) != iProver_top ),
% 11.38/2.00      inference(superposition,[status(thm)],[c_1243,c_1880]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_14,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.38/2.00      | ~ v9_lattices(X1)
% 11.38/2.00      | ~ l3_lattices(X1)
% 11.38/2.00      | v2_struct_0(X1)
% 11.38/2.00      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2 ),
% 11.38/2.00      inference(cnf_transformation,[],[f55]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_982,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.38/2.00      | ~ v9_lattices(X1)
% 11.38/2.00      | ~ l3_lattices(X1)
% 11.38/2.00      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
% 11.38/2.00      | sK7 != X1 ),
% 11.38/2.00      inference(resolution_lifted,[status(thm)],[c_14,c_27]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_983,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.38/2.00      | ~ v9_lattices(sK7)
% 11.38/2.00      | ~ l3_lattices(sK7)
% 11.38/2.00      | k2_lattices(sK7,X0,k1_lattices(sK7,X0,X1)) = X0 ),
% 11.38/2.00      inference(unflattening,[status(thm)],[c_982]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_24,negated_conjecture,
% 11.38/2.00      ( v9_lattices(sK7) ),
% 11.38/2.00      inference(cnf_transformation,[],[f65]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_715,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.38/2.00      | ~ l3_lattices(X1)
% 11.38/2.00      | v2_struct_0(X1)
% 11.38/2.00      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
% 11.38/2.00      | sK7 != X1 ),
% 11.38/2.00      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_716,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.38/2.00      | ~ l3_lattices(sK7)
% 11.38/2.00      | v2_struct_0(sK7)
% 11.38/2.00      | k2_lattices(sK7,X0,k1_lattices(sK7,X0,X1)) = X0 ),
% 11.38/2.00      inference(unflattening,[status(thm)],[c_715]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_720,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.38/2.00      | k2_lattices(sK7,X0,k1_lattices(sK7,X0,X1)) = X0 ),
% 11.38/2.00      inference(global_propositional_subsumption,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_716,c_27,c_23]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_985,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.38/2.00      | k2_lattices(sK7,X0,k1_lattices(sK7,X0,X1)) = X0 ),
% 11.38/2.00      inference(global_propositional_subsumption,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_983,c_27,c_23,c_716]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1092,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0_51,u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(X1_51,u1_struct_0(sK7))
% 11.38/2.00      | k2_lattices(sK7,X0_51,k1_lattices(sK7,X0_51,X1_51)) = X0_51 ),
% 11.38/2.00      inference(subtyping,[status(esa)],[c_985]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1247,plain,
% 11.38/2.00      ( k2_lattices(sK7,X0_51,k1_lattices(sK7,X0_51,X1_51)) = X0_51
% 11.38/2.00      | m1_subset_1(X0_51,u1_struct_0(sK7)) != iProver_top
% 11.38/2.00      | m1_subset_1(X1_51,u1_struct_0(sK7)) != iProver_top ),
% 11.38/2.00      inference(predicate_to_equality,[status(thm)],[c_1092]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1768,plain,
% 11.38/2.00      ( k2_lattices(sK7,sK8,k1_lattices(sK7,sK8,X0_51)) = sK8
% 11.38/2.00      | m1_subset_1(X0_51,u1_struct_0(sK7)) != iProver_top ),
% 11.38/2.00      inference(superposition,[status(thm)],[c_1244,c_1247]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_2170,plain,
% 11.38/2.00      ( k2_lattices(sK7,sK8,k1_lattices(sK7,sK8,sK9)) = sK8 ),
% 11.38/2.00      inference(superposition,[status(thm)],[c_1243,c_1768]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_16,plain,
% 11.38/2.00      ( ~ l3_lattices(X0) | l2_lattices(X0) ),
% 11.38/2.00      inference(cnf_transformation,[],[f61]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1,plain,
% 11.38/2.00      ( ~ r1_lattices(X0,X1,X2)
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.38/2.00      | v2_struct_0(X0)
% 11.38/2.00      | ~ l2_lattices(X0)
% 11.38/2.00      | k1_lattices(X0,X1,X2) = X2 ),
% 11.38/2.00      inference(cnf_transformation,[],[f44]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_283,plain,
% 11.38/2.00      ( ~ r1_lattices(X0,X1,X2)
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.38/2.00      | ~ l3_lattices(X0)
% 11.38/2.00      | v2_struct_0(X0)
% 11.38/2.00      | k1_lattices(X0,X1,X2) = X2 ),
% 11.38/2.00      inference(resolution,[status(thm)],[c_16,c_1]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_19,negated_conjecture,
% 11.38/2.00      ( r1_lattices(sK7,sK8,sK9) ),
% 11.38/2.00      inference(cnf_transformation,[],[f70]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_361,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.38/2.00      | ~ l3_lattices(X1)
% 11.38/2.00      | v2_struct_0(X1)
% 11.38/2.00      | k1_lattices(X1,X2,X0) = X0
% 11.38/2.00      | sK9 != X0
% 11.38/2.00      | sK8 != X2
% 11.38/2.00      | sK7 != X1 ),
% 11.38/2.00      inference(resolution_lifted,[status(thm)],[c_283,c_19]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_362,plain,
% 11.38/2.00      ( ~ m1_subset_1(sK9,u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(sK8,u1_struct_0(sK7))
% 11.38/2.00      | ~ l3_lattices(sK7)
% 11.38/2.00      | v2_struct_0(sK7)
% 11.38/2.00      | k1_lattices(sK7,sK8,sK9) = sK9 ),
% 11.38/2.00      inference(unflattening,[status(thm)],[c_361]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_364,plain,
% 11.38/2.00      ( k1_lattices(sK7,sK8,sK9) = sK9 ),
% 11.38/2.00      inference(global_propositional_subsumption,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_362,c_27,c_23,c_22,c_21]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1094,plain,
% 11.38/2.00      ( k1_lattices(sK7,sK8,sK9) = sK9 ),
% 11.38/2.00      inference(subtyping,[status(esa)],[c_364]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_2172,plain,
% 11.38/2.00      ( k2_lattices(sK7,sK8,sK9) = sK8 ),
% 11.38/2.00      inference(light_normalisation,[status(thm)],[c_2170,c_1094]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_3049,plain,
% 11.38/2.00      ( k2_lattices(sK7,sK8,k2_lattices(sK7,sK9,X0_51)) = k2_lattices(sK7,sK8,X0_51)
% 11.38/2.00      | m1_subset_1(X0_51,u1_struct_0(sK7)) != iProver_top ),
% 11.38/2.00      inference(light_normalisation,[status(thm)],[c_3046,c_2172]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_30022,plain,
% 11.38/2.00      ( k2_lattices(sK7,sK8,k2_lattices(sK7,sK9,sK10)) = k2_lattices(sK7,sK8,sK10) ),
% 11.38/2.00      inference(superposition,[status(thm)],[c_1242,c_3049]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_15,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.38/2.00      | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
% 11.38/2.00      | ~ l1_lattices(X1)
% 11.38/2.00      | v2_struct_0(X1) ),
% 11.38/2.00      inference(cnf_transformation,[],[f59]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_447,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.38/2.00      | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
% 11.38/2.00      | ~ l3_lattices(X3)
% 11.38/2.00      | v2_struct_0(X1)
% 11.38/2.00      | X1 != X3 ),
% 11.38/2.00      inference(resolution_lifted,[status(thm)],[c_17,c_15]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_448,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.38/2.00      | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
% 11.38/2.00      | ~ l3_lattices(X1)
% 11.38/2.00      | v2_struct_0(X1) ),
% 11.38/2.00      inference(unflattening,[status(thm)],[c_447]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_961,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.38/2.00      | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
% 11.38/2.00      | ~ l3_lattices(X1)
% 11.38/2.00      | sK7 != X1 ),
% 11.38/2.00      inference(resolution_lifted,[status(thm)],[c_448,c_27]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_962,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.38/2.00      | m1_subset_1(k2_lattices(sK7,X0,X1),u1_struct_0(sK7))
% 11.38/2.00      | ~ l3_lattices(sK7) ),
% 11.38/2.00      inference(unflattening,[status(thm)],[c_961]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_966,plain,
% 11.38/2.00      ( m1_subset_1(k2_lattices(sK7,X0,X1),u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 11.38/2.00      inference(global_propositional_subsumption,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_962,c_23]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_967,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.38/2.00      | m1_subset_1(k2_lattices(sK7,X0,X1),u1_struct_0(sK7)) ),
% 11.38/2.00      inference(renaming,[status(thm)],[c_966]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1090,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0_51,u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(X1_51,u1_struct_0(sK7))
% 11.38/2.00      | m1_subset_1(k2_lattices(sK7,X0_51,X1_51),u1_struct_0(sK7)) ),
% 11.38/2.00      inference(subtyping,[status(esa)],[c_967]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1249,plain,
% 11.38/2.00      ( m1_subset_1(X0_51,u1_struct_0(sK7)) != iProver_top
% 11.38/2.00      | m1_subset_1(X1_51,u1_struct_0(sK7)) != iProver_top
% 11.38/2.00      | m1_subset_1(k2_lattices(sK7,X0_51,X1_51),u1_struct_0(sK7)) = iProver_top ),
% 11.38/2.00      inference(predicate_to_equality,[status(thm)],[c_1090]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_10,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.38/2.00      | ~ l3_lattices(X1)
% 11.38/2.00      | ~ v8_lattices(X1)
% 11.38/2.00      | v2_struct_0(X1)
% 11.38/2.00      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 ),
% 11.38/2.00      inference(cnf_transformation,[],[f51]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_999,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.38/2.00      | ~ l3_lattices(X1)
% 11.38/2.00      | ~ v8_lattices(X1)
% 11.38/2.00      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
% 11.38/2.00      | sK7 != X1 ),
% 11.38/2.00      inference(resolution_lifted,[status(thm)],[c_10,c_27]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1000,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.38/2.00      | ~ l3_lattices(sK7)
% 11.38/2.00      | ~ v8_lattices(sK7)
% 11.38/2.00      | k1_lattices(sK7,k2_lattices(sK7,X0,X1),X1) = X1 ),
% 11.38/2.00      inference(unflattening,[status(thm)],[c_999]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_25,negated_conjecture,
% 11.38/2.00      ( v8_lattices(sK7) ),
% 11.38/2.00      inference(cnf_transformation,[],[f64]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_601,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.38/2.00      | ~ l3_lattices(X1)
% 11.38/2.00      | v2_struct_0(X1)
% 11.38/2.00      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
% 11.38/2.00      | sK7 != X1 ),
% 11.38/2.00      inference(resolution_lifted,[status(thm)],[c_10,c_25]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_602,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.38/2.00      | ~ l3_lattices(sK7)
% 11.38/2.00      | v2_struct_0(sK7)
% 11.38/2.00      | k1_lattices(sK7,k2_lattices(sK7,X0,X1),X1) = X1 ),
% 11.38/2.00      inference(unflattening,[status(thm)],[c_601]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_606,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.38/2.00      | k1_lattices(sK7,k2_lattices(sK7,X0,X1),X1) = X1 ),
% 11.38/2.00      inference(global_propositional_subsumption,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_602,c_27,c_23]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1002,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 11.38/2.00      | k1_lattices(sK7,k2_lattices(sK7,X0,X1),X1) = X1 ),
% 11.38/2.00      inference(global_propositional_subsumption,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_1000,c_27,c_23,c_602]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1093,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0_51,u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(X1_51,u1_struct_0(sK7))
% 11.38/2.00      | k1_lattices(sK7,k2_lattices(sK7,X0_51,X1_51),X1_51) = X1_51 ),
% 11.38/2.00      inference(subtyping,[status(esa)],[c_1002]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1246,plain,
% 11.38/2.00      ( k1_lattices(sK7,k2_lattices(sK7,X0_51,X1_51),X1_51) = X1_51
% 11.38/2.00      | m1_subset_1(X0_51,u1_struct_0(sK7)) != iProver_top
% 11.38/2.00      | m1_subset_1(X1_51,u1_struct_0(sK7)) != iProver_top ),
% 11.38/2.00      inference(predicate_to_equality,[status(thm)],[c_1093]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1339,plain,
% 11.38/2.00      ( k1_lattices(sK7,k2_lattices(sK7,sK8,X0_51),X0_51) = X0_51
% 11.38/2.00      | m1_subset_1(X0_51,u1_struct_0(sK7)) != iProver_top ),
% 11.38/2.00      inference(superposition,[status(thm)],[c_1244,c_1246]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_2367,plain,
% 11.38/2.00      ( k1_lattices(sK7,k2_lattices(sK7,sK8,k2_lattices(sK7,X0_51,X1_51)),k2_lattices(sK7,X0_51,X1_51)) = k2_lattices(sK7,X0_51,X1_51)
% 11.38/2.00      | m1_subset_1(X0_51,u1_struct_0(sK7)) != iProver_top
% 11.38/2.00      | m1_subset_1(X1_51,u1_struct_0(sK7)) != iProver_top ),
% 11.38/2.00      inference(superposition,[status(thm)],[c_1249,c_1339]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_8870,plain,
% 11.38/2.00      ( k1_lattices(sK7,k2_lattices(sK7,sK8,k2_lattices(sK7,sK9,X0_51)),k2_lattices(sK7,sK9,X0_51)) = k2_lattices(sK7,sK9,X0_51)
% 11.38/2.00      | m1_subset_1(X0_51,u1_struct_0(sK7)) != iProver_top ),
% 11.38/2.00      inference(superposition,[status(thm)],[c_1243,c_2367]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_9928,plain,
% 11.38/2.00      ( k1_lattices(sK7,k2_lattices(sK7,sK8,k2_lattices(sK7,sK9,sK10)),k2_lattices(sK7,sK9,sK10)) = k2_lattices(sK7,sK9,sK10) ),
% 11.38/2.00      inference(superposition,[status(thm)],[c_1242,c_8870]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_30233,plain,
% 11.38/2.00      ( k1_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10)) = k2_lattices(sK7,sK9,sK10) ),
% 11.38/2.00      inference(demodulation,[status(thm)],[c_30022,c_9928]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1277,plain,
% 11.38/2.00      ( m1_subset_1(k2_lattices(sK7,sK8,sK10),u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(sK10,u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
% 11.38/2.00      inference(instantiation,[status(thm)],[c_1090]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1271,plain,
% 11.38/2.00      ( m1_subset_1(k2_lattices(sK7,sK9,sK10),u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(sK9,u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(sK10,u1_struct_0(sK7)) ),
% 11.38/2.00      inference(instantiation,[status(thm)],[c_1090]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_0,plain,
% 11.38/2.00      ( r1_lattices(X0,X1,X2)
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.38/2.00      | v2_struct_0(X0)
% 11.38/2.00      | ~ l2_lattices(X0)
% 11.38/2.00      | k1_lattices(X0,X1,X2) != X2 ),
% 11.38/2.00      inference(cnf_transformation,[],[f45]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_306,plain,
% 11.38/2.00      ( r1_lattices(X0,X1,X2)
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.38/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.38/2.00      | ~ l3_lattices(X0)
% 11.38/2.00      | v2_struct_0(X0)
% 11.38/2.00      | k1_lattices(X0,X1,X2) != X2 ),
% 11.38/2.00      inference(resolution,[status(thm)],[c_16,c_0]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_18,negated_conjecture,
% 11.38/2.00      ( ~ r1_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10)) ),
% 11.38/2.00      inference(cnf_transformation,[],[f71]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_344,plain,
% 11.38/2.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.38/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.38/2.00      | ~ l3_lattices(X1)
% 11.38/2.00      | v2_struct_0(X1)
% 11.38/2.00      | k2_lattices(sK7,sK9,sK10) != X0
% 11.38/2.00      | k2_lattices(sK7,sK8,sK10) != X2
% 11.38/2.00      | k1_lattices(X1,X2,X0) != X0
% 11.38/2.00      | sK7 != X1 ),
% 11.38/2.00      inference(resolution_lifted,[status(thm)],[c_306,c_18]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_345,plain,
% 11.38/2.00      ( ~ m1_subset_1(k2_lattices(sK7,sK9,sK10),u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(k2_lattices(sK7,sK8,sK10),u1_struct_0(sK7))
% 11.38/2.00      | ~ l3_lattices(sK7)
% 11.38/2.00      | v2_struct_0(sK7)
% 11.38/2.00      | k1_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10)) != k2_lattices(sK7,sK9,sK10) ),
% 11.38/2.00      inference(unflattening,[status(thm)],[c_344]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_347,plain,
% 11.38/2.00      ( ~ m1_subset_1(k2_lattices(sK7,sK9,sK10),u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(k2_lattices(sK7,sK8,sK10),u1_struct_0(sK7))
% 11.38/2.00      | k1_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10)) != k2_lattices(sK7,sK9,sK10) ),
% 11.38/2.00      inference(global_propositional_subsumption,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_345,c_27,c_23]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(c_1095,plain,
% 11.38/2.00      ( ~ m1_subset_1(k2_lattices(sK7,sK9,sK10),u1_struct_0(sK7))
% 11.38/2.00      | ~ m1_subset_1(k2_lattices(sK7,sK8,sK10),u1_struct_0(sK7))
% 11.38/2.00      | k1_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10)) != k2_lattices(sK7,sK9,sK10) ),
% 11.38/2.00      inference(subtyping,[status(esa)],[c_347]) ).
% 11.38/2.00  
% 11.38/2.00  cnf(contradiction,plain,
% 11.38/2.00      ( $false ),
% 11.38/2.00      inference(minisat,
% 11.38/2.00                [status(thm)],
% 11.38/2.00                [c_30233,c_1277,c_1271,c_1095,c_20,c_21,c_22]) ).
% 11.38/2.00  
% 11.38/2.00  
% 11.38/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.38/2.00  
% 11.38/2.00  ------                               Statistics
% 11.38/2.00  
% 11.38/2.00  ------ General
% 11.38/2.00  
% 11.38/2.00  abstr_ref_over_cycles:                  0
% 11.38/2.00  abstr_ref_under_cycles:                 0
% 11.38/2.00  gc_basic_clause_elim:                   0
% 11.38/2.00  forced_gc_time:                         0
% 11.38/2.00  parsing_time:                           0.006
% 11.38/2.00  unif_index_cands_time:                  0.
% 11.38/2.00  unif_index_add_time:                    0.
% 11.38/2.00  orderings_time:                         0.
% 11.38/2.00  out_proof_time:                         0.011
% 11.38/2.00  total_time:                             1.258
% 11.38/2.00  num_of_symbols:                         54
% 11.38/2.00  num_of_terms:                           30987
% 11.38/2.00  
% 11.38/2.00  ------ Preprocessing
% 11.38/2.00  
% 11.38/2.00  num_of_splits:                          0
% 11.38/2.00  num_of_split_atoms:                     0
% 11.38/2.00  num_of_reused_defs:                     0
% 11.38/2.00  num_eq_ax_congr_red:                    14
% 11.38/2.00  num_of_sem_filtered_clauses:            1
% 11.38/2.00  num_of_subtypes:                        3
% 11.38/2.00  monotx_restored_types:                  0
% 11.38/2.00  sat_num_of_epr_types:                   0
% 11.38/2.00  sat_num_of_non_cyclic_types:            0
% 11.38/2.00  sat_guarded_non_collapsed_types:        1
% 11.38/2.00  num_pure_diseq_elim:                    0
% 11.38/2.00  simp_replaced_by:                       0
% 11.38/2.00  res_preprocessed:                       69
% 11.38/2.00  prep_upred:                             0
% 11.38/2.00  prep_unflattend:                        35
% 11.38/2.00  smt_new_axioms:                         0
% 11.38/2.00  pred_elim_cands:                        1
% 11.38/2.00  pred_elim:                              8
% 11.38/2.00  pred_elim_cl:                           18
% 11.38/2.00  pred_elim_cycles:                       13
% 11.38/2.00  merged_defs:                            0
% 11.38/2.00  merged_defs_ncl:                        0
% 11.38/2.00  bin_hyper_res:                          0
% 11.38/2.00  prep_cycles:                            4
% 11.38/2.00  pred_elim_time:                         0.009
% 11.38/2.00  splitting_time:                         0.
% 11.38/2.00  sem_filter_time:                        0.
% 11.38/2.00  monotx_time:                            0.
% 11.38/2.00  subtype_inf_time:                       0.
% 11.38/2.00  
% 11.38/2.00  ------ Problem properties
% 11.38/2.00  
% 11.38/2.00  clauses:                                10
% 11.38/2.00  conjectures:                            3
% 11.38/2.00  epr:                                    0
% 11.38/2.00  horn:                                   10
% 11.38/2.00  ground:                                 6
% 11.38/2.00  unary:                                  4
% 11.38/2.00  binary:                                 1
% 11.38/2.00  lits:                                   22
% 11.38/2.00  lits_eq:                                7
% 11.38/2.00  fd_pure:                                0
% 11.38/2.00  fd_pseudo:                              0
% 11.38/2.00  fd_cond:                                0
% 11.38/2.00  fd_pseudo_cond:                         0
% 11.38/2.00  ac_symbols:                             0
% 11.38/2.00  
% 11.38/2.00  ------ Propositional Solver
% 11.38/2.00  
% 11.38/2.00  prop_solver_calls:                      37
% 11.38/2.00  prop_fast_solver_calls:                 1101
% 11.38/2.00  smt_solver_calls:                       0
% 11.38/2.00  smt_fast_solver_calls:                  0
% 11.38/2.00  prop_num_of_clauses:                    12137
% 11.38/2.00  prop_preprocess_simplified:             19329
% 11.38/2.00  prop_fo_subsumed:                       33
% 11.38/2.00  prop_solver_time:                       0.
% 11.38/2.00  smt_solver_time:                        0.
% 11.38/2.00  smt_fast_solver_time:                   0.
% 11.38/2.00  prop_fast_solver_time:                  0.
% 11.38/2.00  prop_unsat_core_time:                   0.001
% 11.38/2.00  
% 11.38/2.00  ------ QBF
% 11.38/2.00  
% 11.38/2.00  qbf_q_res:                              0
% 11.38/2.00  qbf_num_tautologies:                    0
% 11.38/2.00  qbf_prep_cycles:                        0
% 11.38/2.00  
% 11.38/2.00  ------ BMC1
% 11.38/2.00  
% 11.38/2.00  bmc1_current_bound:                     -1
% 11.38/2.00  bmc1_last_solved_bound:                 -1
% 11.38/2.00  bmc1_unsat_core_size:                   -1
% 11.38/2.00  bmc1_unsat_core_parents_size:           -1
% 11.38/2.00  bmc1_merge_next_fun:                    0
% 11.38/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.38/2.00  
% 11.38/2.00  ------ Instantiation
% 11.38/2.00  
% 11.38/2.00  inst_num_of_clauses:                    4692
% 11.38/2.00  inst_num_in_passive:                    1821
% 11.38/2.00  inst_num_in_active:                     1617
% 11.38/2.00  inst_num_in_unprocessed:                1254
% 11.38/2.00  inst_num_of_loops:                      1740
% 11.38/2.00  inst_num_of_learning_restarts:          0
% 11.38/2.00  inst_num_moves_active_passive:          115
% 11.38/2.00  inst_lit_activity:                      0
% 11.38/2.00  inst_lit_activity_moves:                1
% 11.38/2.00  inst_num_tautologies:                   0
% 11.38/2.00  inst_num_prop_implied:                  0
% 11.38/2.00  inst_num_existing_simplified:           0
% 11.38/2.00  inst_num_eq_res_simplified:             0
% 11.38/2.00  inst_num_child_elim:                    0
% 11.38/2.00  inst_num_of_dismatching_blockings:      4588
% 11.38/2.00  inst_num_of_non_proper_insts:           7530
% 11.38/2.00  inst_num_of_duplicates:                 0
% 11.38/2.00  inst_inst_num_from_inst_to_res:         0
% 11.38/2.00  inst_dismatching_checking_time:         0.
% 11.38/2.00  
% 11.38/2.00  ------ Resolution
% 11.38/2.00  
% 11.38/2.00  res_num_of_clauses:                     0
% 11.38/2.00  res_num_in_passive:                     0
% 11.38/2.00  res_num_in_active:                      0
% 11.38/2.00  res_num_of_loops:                       73
% 11.38/2.00  res_forward_subset_subsumed:            747
% 11.38/2.00  res_backward_subset_subsumed:           2
% 11.38/2.00  res_forward_subsumed:                   0
% 11.38/2.00  res_backward_subsumed:                  0
% 11.38/2.00  res_forward_subsumption_resolution:     0
% 11.38/2.00  res_backward_subsumption_resolution:    0
% 11.38/2.00  res_clause_to_clause_subsumption:       3053
% 11.38/2.00  res_orphan_elimination:                 0
% 11.38/2.00  res_tautology_del:                      517
% 11.38/2.00  res_num_eq_res_simplified:              1
% 11.38/2.00  res_num_sel_changes:                    0
% 11.38/2.00  res_moves_from_active_to_pass:          0
% 11.38/2.00  
% 11.38/2.00  ------ Superposition
% 11.38/2.00  
% 11.38/2.00  sup_time_total:                         0.
% 11.38/2.00  sup_time_generating:                    0.
% 11.38/2.00  sup_time_sim_full:                      0.
% 11.38/2.00  sup_time_sim_immed:                     0.
% 11.38/2.00  
% 11.38/2.00  sup_num_of_clauses:                     1206
% 11.38/2.00  sup_num_in_active:                      329
% 11.38/2.00  sup_num_in_passive:                     877
% 11.38/2.00  sup_num_of_loops:                       346
% 11.38/2.00  sup_fw_superposition:                   612
% 11.38/2.00  sup_bw_superposition:                   741
% 11.38/2.00  sup_immediate_simplified:               375
% 11.38/2.00  sup_given_eliminated:                   0
% 11.38/2.00  comparisons_done:                       0
% 11.38/2.00  comparisons_avoided:                    0
% 11.38/2.00  
% 11.38/2.00  ------ Simplifications
% 11.38/2.00  
% 11.38/2.00  
% 11.38/2.00  sim_fw_subset_subsumed:                 81
% 11.38/2.00  sim_bw_subset_subsumed:                 3
% 11.38/2.00  sim_fw_subsumed:                        3
% 11.38/2.00  sim_bw_subsumed:                        0
% 11.38/2.00  sim_fw_subsumption_res:                 0
% 11.38/2.00  sim_bw_subsumption_res:                 0
% 11.38/2.00  sim_tautology_del:                      10
% 11.38/2.00  sim_eq_tautology_del:                   17
% 11.38/2.00  sim_eq_res_simp:                        0
% 11.38/2.00  sim_fw_demodulated:                     115
% 11.38/2.00  sim_bw_demodulated:                     17
% 11.38/2.00  sim_light_normalised:                   193
% 11.38/2.00  sim_joinable_taut:                      0
% 11.38/2.00  sim_joinable_simp:                      0
% 11.38/2.00  sim_ac_normalised:                      0
% 11.38/2.00  sim_smt_subsumption:                    0
% 11.38/2.00  
%------------------------------------------------------------------------------
