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
% DateTime   : Thu Dec  3 12:13:13 EST 2020

% Result     : Theorem 15.33s
% Output     : CNFRefutation 15.33s
% Verified   : 
% Statistics : Number of formulae       :  158 (1408 expanded)
%              Number of clauses        :   97 ( 328 expanded)
%              Number of leaves         :   18 ( 496 expanded)
%              Depth                    :   24
%              Number of atoms          :  711 (10453 expanded)
%              Number of equality atoms :  172 ( 498 expanded)
%              Maximal formula depth    :   12 (   5 average)
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
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
          & r1_lattices(X0,X1,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,k2_lattices(X0,X1,sK10),k2_lattices(X0,X2,sK10))
        & r1_lattices(X0,X1,X2)
        & m1_subset_1(sK10,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f44,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f22,f43,f42,f41,f40])).

fof(f69,plain,(
    m1_subset_1(sK10,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
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

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f1])).

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
    inference(flattening,[],[f10])).

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
    inference(nnf_transformation,[],[f11])).

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

fof(f45,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    l3_lattices(sK7) ),
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    v7_lattices(sK7) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
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

fof(f14,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

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
    inference(flattening,[],[f14])).

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
    inference(nnf_transformation,[],[f15])).

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

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
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

fof(f12,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

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
    inference(flattening,[],[f12])).

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
    inference(nnf_transformation,[],[f13])).

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

fof(f50,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f44])).

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
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    r1_lattices(sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f44])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k2_lattices(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f71,plain,(
    ~ r1_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1026,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1171,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1026])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1025,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1172,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1025])).

cnf(c_14,plain,
    ( ~ l3_lattices(X0)
    | l1_lattices(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_lattices(X1)
    | ~ v7_lattices(X1)
    | k2_lattices(X1,k2_lattices(X1,X3,X2),X0) = k2_lattices(X1,X3,k2_lattices(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_352,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X4)
    | v2_struct_0(X1)
    | ~ v7_lattices(X1)
    | X1 != X4
    | k2_lattices(X1,X3,k2_lattices(X1,X2,X0)) = k2_lattices(X1,k2_lattices(X1,X3,X2),X0) ),
    inference(resolution_lifted,[status(thm)],[c_14,c_4])).

cnf(c_353,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v7_lattices(X1)
    | k2_lattices(X1,X3,k2_lattices(X1,X2,X0)) = k2_lattices(X1,k2_lattices(X1,X3,X2),X0) ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_869,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v7_lattices(X1)
    | k2_lattices(X1,X3,k2_lattices(X1,X2,X0)) = k2_lattices(X1,k2_lattices(X1,X3,X2),X0)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_353,c_26])).

cnf(c_870,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | ~ v7_lattices(sK7)
    | k2_lattices(sK7,X2,k2_lattices(sK7,X0,X1)) = k2_lattices(sK7,k2_lattices(sK7,X2,X0),X1) ),
    inference(unflattening,[status(thm)],[c_869])).

cnf(c_22,negated_conjecture,
    ( l3_lattices(sK7) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_25,negated_conjecture,
    ( v7_lattices(sK7) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_793,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X3,k2_lattices(X1,X2,X0)) = k2_lattices(X1,k2_lattices(X1,X3,X2),X0)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_353,c_25])).

cnf(c_794,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k2_lattices(sK7,X2,k2_lattices(sK7,X0,X1)) = k2_lattices(sK7,k2_lattices(sK7,X2,X0),X1) ),
    inference(unflattening,[status(thm)],[c_793])).

cnf(c_872,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | k2_lattices(sK7,X2,k2_lattices(sK7,X0,X1)) = k2_lattices(sK7,k2_lattices(sK7,X2,X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_870,c_26,c_22,c_794])).

cnf(c_873,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | k2_lattices(sK7,X0,k2_lattices(sK7,X1,X2)) = k2_lattices(sK7,k2_lattices(sK7,X0,X1),X2) ),
    inference(renaming,[status(thm)],[c_872])).

cnf(c_1019,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK7))
    | ~ m1_subset_1(X2_50,u1_struct_0(sK7))
    | k2_lattices(sK7,X0_50,k2_lattices(sK7,X1_50,X2_50)) = k2_lattices(sK7,k2_lattices(sK7,X0_50,X1_50),X2_50) ),
    inference(subtyping,[status(esa)],[c_873])).

cnf(c_1177,plain,
    ( k2_lattices(sK7,X0_50,k2_lattices(sK7,X1_50,X2_50)) = k2_lattices(sK7,k2_lattices(sK7,X0_50,X1_50),X2_50)
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X2_50,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1019])).

cnf(c_1854,plain,
    ( k2_lattices(sK7,k2_lattices(sK7,sK9,X0_50),X1_50) = k2_lattices(sK7,sK9,k2_lattices(sK7,X0_50,X1_50))
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1172,c_1177])).

cnf(c_2772,plain,
    ( k2_lattices(sK7,sK9,k2_lattices(sK7,sK10,X0_50)) = k2_lattices(sK7,k2_lattices(sK7,sK9,sK10),X0_50)
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1171,c_1854])).

cnf(c_3741,plain,
    ( k2_lattices(sK7,sK9,k2_lattices(sK7,sK10,sK10)) = k2_lattices(sK7,k2_lattices(sK7,sK9,sK10),sK10) ),
    inference(superposition,[status(thm)],[c_1171,c_2772])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_lattices(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_331,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_13])).

cnf(c_332,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_889,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_332,c_26])).

cnf(c_890,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(k2_lattices(sK7,X0,X1),u1_struct_0(sK7))
    | ~ l3_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_889])).

cnf(c_894,plain,
    ( m1_subset_1(k2_lattices(sK7,X0,X1),u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_890,c_22])).

cnf(c_895,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(k2_lattices(sK7,X0,X1),u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_894])).

cnf(c_1018,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK7))
    | m1_subset_1(k2_lattices(sK7,X0_50,X1_50),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_895])).

cnf(c_1178,plain,
    ( m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k2_lattices(sK7,X0_50,X1_50),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1018])).

cnf(c_3761,plain,
    ( m1_subset_1(k2_lattices(sK7,sK9,k2_lattices(sK7,sK10,sK10)),u1_struct_0(sK7)) = iProver_top
    | m1_subset_1(k2_lattices(sK7,sK9,sK10),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3741,c_1178])).

cnf(c_33,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_34,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1240,plain,
    ( m1_subset_1(k2_lattices(sK7,sK9,sK10),u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK10,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_1018])).

cnf(c_1241,plain,
    ( m1_subset_1(k2_lattices(sK7,sK9,sK10),u1_struct_0(sK7)) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1240])).

cnf(c_51677,plain,
    ( m1_subset_1(k2_lattices(sK7,sK9,k2_lattices(sK7,sK10,sK10)),u1_struct_0(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3761,c_33,c_34,c_1241])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_910,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_26])).

cnf(c_911,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ v9_lattices(sK7)
    | ~ l3_lattices(sK7)
    | k2_lattices(sK7,X0,k1_lattices(sK7,X0,X1)) = X0 ),
    inference(unflattening,[status(thm)],[c_910])).

cnf(c_23,negated_conjecture,
    ( v9_lattices(sK7) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_643,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_23])).

cnf(c_644,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k2_lattices(sK7,X0,k1_lattices(sK7,X0,X1)) = X0 ),
    inference(unflattening,[status(thm)],[c_643])).

cnf(c_648,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | k2_lattices(sK7,X0,k1_lattices(sK7,X0,X1)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_644,c_26,c_22])).

cnf(c_913,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | k2_lattices(sK7,X0,k1_lattices(sK7,X0,X1)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_911,c_26,c_22,c_644])).

cnf(c_1020,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK7))
    | k2_lattices(sK7,X0_50,k1_lattices(sK7,X0_50,X1_50)) = X0_50 ),
    inference(subtyping,[status(esa)],[c_913])).

cnf(c_1176,plain,
    ( k2_lattices(sK7,X0_50,k1_lattices(sK7,X0_50,X1_50)) = X0_50
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1020])).

cnf(c_2591,plain,
    ( k2_lattices(sK7,k2_lattices(sK7,X0_50,X1_50),k1_lattices(sK7,k2_lattices(sK7,X0_50,X1_50),X2_50)) = k2_lattices(sK7,X0_50,X1_50)
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X2_50,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1178,c_1176])).

cnf(c_8792,plain,
    ( k2_lattices(sK7,k2_lattices(sK7,sK9,X0_50),k1_lattices(sK7,k2_lattices(sK7,sK9,X0_50),X1_50)) = k2_lattices(sK7,sK9,X0_50)
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1172,c_2591])).

cnf(c_9851,plain,
    ( k2_lattices(sK7,k2_lattices(sK7,sK9,sK10),k1_lattices(sK7,k2_lattices(sK7,sK9,sK10),X0_50)) = k2_lattices(sK7,sK9,sK10)
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1171,c_8792])).

cnf(c_10016,plain,
    ( k2_lattices(sK7,k2_lattices(sK7,sK9,sK10),k1_lattices(sK7,k2_lattices(sK7,sK9,sK10),sK10)) = k2_lattices(sK7,sK9,sK10) ),
    inference(superposition,[status(thm)],[c_1171,c_9851])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v8_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_927,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v8_lattices(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_26])).

cnf(c_928,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | ~ v8_lattices(sK7)
    | k1_lattices(sK7,k2_lattices(sK7,X0,X1),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_927])).

cnf(c_24,negated_conjecture,
    ( v8_lattices(sK7) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_529,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_530,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k1_lattices(sK7,k2_lattices(sK7,X0,X1),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_529])).

cnf(c_534,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | k1_lattices(sK7,k2_lattices(sK7,X0,X1),X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_530,c_26,c_22])).

cnf(c_930,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | k1_lattices(sK7,k2_lattices(sK7,X0,X1),X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_928,c_26,c_22,c_530])).

cnf(c_1021,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK7))
    | k1_lattices(sK7,k2_lattices(sK7,X0_50,X1_50),X1_50) = X1_50 ),
    inference(subtyping,[status(esa)],[c_930])).

cnf(c_1175,plain,
    ( k1_lattices(sK7,k2_lattices(sK7,X0_50,X1_50),X1_50) = X1_50
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1021])).

cnf(c_1319,plain,
    ( k1_lattices(sK7,k2_lattices(sK7,sK9,X0_50),X0_50) = X0_50
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1172,c_1175])).

cnf(c_1497,plain,
    ( k1_lattices(sK7,k2_lattices(sK7,sK9,sK10),sK10) = sK10 ),
    inference(superposition,[status(thm)],[c_1171,c_1319])).

cnf(c_10031,plain,
    ( k2_lattices(sK7,sK9,k2_lattices(sK7,sK10,sK10)) = k2_lattices(sK7,sK9,sK10) ),
    inference(light_normalisation,[status(thm)],[c_10016,c_1497,c_3741])).

cnf(c_51681,plain,
    ( m1_subset_1(k2_lattices(sK7,sK9,sK10),u1_struct_0(sK7)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_51677,c_10031])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1024,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1173,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1024])).

cnf(c_8793,plain,
    ( k2_lattices(sK7,k2_lattices(sK7,sK8,X0_50),k1_lattices(sK7,k2_lattices(sK7,sK8,X0_50),X1_50)) = k2_lattices(sK7,sK8,X0_50)
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1173,c_2591])).

cnf(c_16046,plain,
    ( k2_lattices(sK7,k2_lattices(sK7,sK8,sK10),k1_lattices(sK7,k2_lattices(sK7,sK8,sK10),X0_50)) = k2_lattices(sK7,sK8,sK10)
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1171,c_8793])).

cnf(c_51731,plain,
    ( k2_lattices(sK7,k2_lattices(sK7,sK8,sK10),k1_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10))) = k2_lattices(sK7,sK8,sK10) ),
    inference(superposition,[status(thm)],[c_51681,c_16046])).

cnf(c_1320,plain,
    ( k1_lattices(sK7,k2_lattices(sK7,sK8,X0_50),X0_50) = X0_50
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1173,c_1175])).

cnf(c_2592,plain,
    ( k1_lattices(sK7,k2_lattices(sK7,sK8,k2_lattices(sK7,X0_50,X1_50)),k2_lattices(sK7,X0_50,X1_50)) = k2_lattices(sK7,X0_50,X1_50)
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1178,c_1320])).

cnf(c_10041,plain,
    ( k1_lattices(sK7,k2_lattices(sK7,sK8,k2_lattices(sK7,sK9,X0_50)),k2_lattices(sK7,sK9,X0_50)) = k2_lattices(sK7,sK9,X0_50)
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1172,c_2592])).

cnf(c_11181,plain,
    ( k1_lattices(sK7,k2_lattices(sK7,sK8,k2_lattices(sK7,sK9,sK10)),k2_lattices(sK7,sK9,sK10)) = k2_lattices(sK7,sK9,sK10) ),
    inference(superposition,[status(thm)],[c_1171,c_10041])).

cnf(c_1855,plain,
    ( k2_lattices(sK7,k2_lattices(sK7,sK8,X0_50),X1_50) = k2_lattices(sK7,sK8,k2_lattices(sK7,X0_50,X1_50))
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1173,c_1177])).

cnf(c_3545,plain,
    ( k2_lattices(sK7,sK8,k2_lattices(sK7,sK9,X0_50)) = k2_lattices(sK7,k2_lattices(sK7,sK8,sK9),X0_50)
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1172,c_1855])).

cnf(c_16,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v9_lattices(X0)
    | ~ l3_lattices(X0)
    | ~ v8_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_18,negated_conjecture,
    ( r1_lattices(sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_431,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ v8_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = X2
    | sK9 != X0
    | sK8 != X2
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_18])).

cnf(c_432,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7))
    | ~ v9_lattices(sK7)
    | ~ l3_lattices(sK7)
    | ~ v8_lattices(sK7)
    | v2_struct_0(sK7)
    | k2_lattices(sK7,sK8,sK9) = sK8 ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_434,plain,
    ( k2_lattices(sK7,sK8,sK9) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_432,c_26,c_24,c_23,c_22,c_21,c_20])).

cnf(c_1022,plain,
    ( k2_lattices(sK7,sK8,sK9) = sK8 ),
    inference(subtyping,[status(esa)],[c_434])).

cnf(c_3562,plain,
    ( k2_lattices(sK7,sK8,k2_lattices(sK7,sK9,X0_50)) = k2_lattices(sK7,sK8,X0_50)
    | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3545,c_1022])).

cnf(c_4016,plain,
    ( k2_lattices(sK7,sK8,k2_lattices(sK7,sK9,sK10)) = k2_lattices(sK7,sK8,sK10) ),
    inference(superposition,[status(thm)],[c_1171,c_3562])).

cnf(c_11198,plain,
    ( k1_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10)) = k2_lattices(sK7,sK9,sK10) ),
    inference(light_normalisation,[status(thm)],[c_11181,c_4016])).

cnf(c_51952,plain,
    ( k2_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10)) = k2_lattices(sK7,sK8,sK10) ),
    inference(light_normalisation,[status(thm)],[c_51731,c_11198])).

cnf(c_1288,plain,
    ( m1_subset_1(k2_lattices(sK7,sK8,sK10),u1_struct_0(sK7))
    | ~ m1_subset_1(sK10,u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_1018])).

cnf(c_15,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v9_lattices(X0)
    | ~ l3_lattices(X0)
    | ~ v8_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) != X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_17,negated_conjecture,
    ( ~ r1_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_414,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ v8_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) != X2
    | k2_lattices(sK7,sK9,sK10) != X0
    | k2_lattices(sK7,sK8,sK10) != X2
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_17])).

cnf(c_415,plain,
    ( ~ m1_subset_1(k2_lattices(sK7,sK9,sK10),u1_struct_0(sK7))
    | ~ m1_subset_1(k2_lattices(sK7,sK8,sK10),u1_struct_0(sK7))
    | ~ v9_lattices(sK7)
    | ~ l3_lattices(sK7)
    | ~ v8_lattices(sK7)
    | v2_struct_0(sK7)
    | k2_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10)) != k2_lattices(sK7,sK8,sK10) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_417,plain,
    ( ~ m1_subset_1(k2_lattices(sK7,sK9,sK10),u1_struct_0(sK7))
    | ~ m1_subset_1(k2_lattices(sK7,sK8,sK10),u1_struct_0(sK7))
    | k2_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10)) != k2_lattices(sK7,sK8,sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_26,c_24,c_23,c_22])).

cnf(c_1023,plain,
    ( ~ m1_subset_1(k2_lattices(sK7,sK9,sK10),u1_struct_0(sK7))
    | ~ m1_subset_1(k2_lattices(sK7,sK8,sK10),u1_struct_0(sK7))
    | k2_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10)) != k2_lattices(sK7,sK8,sK10) ),
    inference(subtyping,[status(esa)],[c_417])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_51952,c_1288,c_1240,c_1023,c_19,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:07:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.33/2.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.33/2.51  
% 15.33/2.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.33/2.51  
% 15.33/2.51  ------  iProver source info
% 15.33/2.51  
% 15.33/2.51  git: date: 2020-06-30 10:37:57 +0100
% 15.33/2.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.33/2.51  git: non_committed_changes: false
% 15.33/2.51  git: last_make_outside_of_git: false
% 15.33/2.51  
% 15.33/2.51  ------ 
% 15.33/2.51  
% 15.33/2.51  ------ Input Options
% 15.33/2.51  
% 15.33/2.51  --out_options                           all
% 15.33/2.51  --tptp_safe_out                         true
% 15.33/2.51  --problem_path                          ""
% 15.33/2.51  --include_path                          ""
% 15.33/2.51  --clausifier                            res/vclausify_rel
% 15.33/2.51  --clausifier_options                    --mode clausify
% 15.33/2.51  --stdin                                 false
% 15.33/2.51  --stats_out                             all
% 15.33/2.51  
% 15.33/2.51  ------ General Options
% 15.33/2.51  
% 15.33/2.51  --fof                                   false
% 15.33/2.51  --time_out_real                         305.
% 15.33/2.51  --time_out_virtual                      -1.
% 15.33/2.51  --symbol_type_check                     false
% 15.33/2.51  --clausify_out                          false
% 15.33/2.51  --sig_cnt_out                           false
% 15.33/2.51  --trig_cnt_out                          false
% 15.33/2.51  --trig_cnt_out_tolerance                1.
% 15.33/2.51  --trig_cnt_out_sk_spl                   false
% 15.33/2.51  --abstr_cl_out                          false
% 15.33/2.51  
% 15.33/2.51  ------ Global Options
% 15.33/2.51  
% 15.33/2.51  --schedule                              default
% 15.33/2.51  --add_important_lit                     false
% 15.33/2.51  --prop_solver_per_cl                    1000
% 15.33/2.51  --min_unsat_core                        false
% 15.33/2.51  --soft_assumptions                      false
% 15.33/2.51  --soft_lemma_size                       3
% 15.33/2.51  --prop_impl_unit_size                   0
% 15.33/2.51  --prop_impl_unit                        []
% 15.33/2.51  --share_sel_clauses                     true
% 15.33/2.51  --reset_solvers                         false
% 15.33/2.51  --bc_imp_inh                            [conj_cone]
% 15.33/2.51  --conj_cone_tolerance                   3.
% 15.33/2.51  --extra_neg_conj                        none
% 15.33/2.51  --large_theory_mode                     true
% 15.33/2.51  --prolific_symb_bound                   200
% 15.33/2.51  --lt_threshold                          2000
% 15.33/2.51  --clause_weak_htbl                      true
% 15.33/2.51  --gc_record_bc_elim                     false
% 15.33/2.51  
% 15.33/2.51  ------ Preprocessing Options
% 15.33/2.51  
% 15.33/2.51  --preprocessing_flag                    true
% 15.33/2.51  --time_out_prep_mult                    0.1
% 15.33/2.51  --splitting_mode                        input
% 15.33/2.51  --splitting_grd                         true
% 15.33/2.51  --splitting_cvd                         false
% 15.33/2.51  --splitting_cvd_svl                     false
% 15.33/2.51  --splitting_nvd                         32
% 15.33/2.51  --sub_typing                            true
% 15.33/2.51  --prep_gs_sim                           true
% 15.33/2.51  --prep_unflatten                        true
% 15.33/2.51  --prep_res_sim                          true
% 15.33/2.51  --prep_upred                            true
% 15.33/2.51  --prep_sem_filter                       exhaustive
% 15.33/2.51  --prep_sem_filter_out                   false
% 15.33/2.51  --pred_elim                             true
% 15.33/2.51  --res_sim_input                         true
% 15.33/2.51  --eq_ax_congr_red                       true
% 15.33/2.51  --pure_diseq_elim                       true
% 15.33/2.51  --brand_transform                       false
% 15.33/2.51  --non_eq_to_eq                          false
% 15.33/2.51  --prep_def_merge                        true
% 15.33/2.51  --prep_def_merge_prop_impl              false
% 15.33/2.51  --prep_def_merge_mbd                    true
% 15.33/2.51  --prep_def_merge_tr_red                 false
% 15.33/2.51  --prep_def_merge_tr_cl                  false
% 15.33/2.51  --smt_preprocessing                     true
% 15.33/2.51  --smt_ac_axioms                         fast
% 15.33/2.51  --preprocessed_out                      false
% 15.33/2.51  --preprocessed_stats                    false
% 15.33/2.51  
% 15.33/2.51  ------ Abstraction refinement Options
% 15.33/2.51  
% 15.33/2.51  --abstr_ref                             []
% 15.33/2.51  --abstr_ref_prep                        false
% 15.33/2.51  --abstr_ref_until_sat                   false
% 15.33/2.51  --abstr_ref_sig_restrict                funpre
% 15.33/2.51  --abstr_ref_af_restrict_to_split_sk     false
% 15.33/2.51  --abstr_ref_under                       []
% 15.33/2.51  
% 15.33/2.51  ------ SAT Options
% 15.33/2.51  
% 15.33/2.51  --sat_mode                              false
% 15.33/2.51  --sat_fm_restart_options                ""
% 15.33/2.51  --sat_gr_def                            false
% 15.33/2.51  --sat_epr_types                         true
% 15.33/2.51  --sat_non_cyclic_types                  false
% 15.33/2.51  --sat_finite_models                     false
% 15.33/2.51  --sat_fm_lemmas                         false
% 15.33/2.51  --sat_fm_prep                           false
% 15.33/2.51  --sat_fm_uc_incr                        true
% 15.33/2.51  --sat_out_model                         small
% 15.33/2.51  --sat_out_clauses                       false
% 15.33/2.51  
% 15.33/2.51  ------ QBF Options
% 15.33/2.51  
% 15.33/2.51  --qbf_mode                              false
% 15.33/2.51  --qbf_elim_univ                         false
% 15.33/2.51  --qbf_dom_inst                          none
% 15.33/2.51  --qbf_dom_pre_inst                      false
% 15.33/2.51  --qbf_sk_in                             false
% 15.33/2.51  --qbf_pred_elim                         true
% 15.33/2.51  --qbf_split                             512
% 15.33/2.51  
% 15.33/2.51  ------ BMC1 Options
% 15.33/2.51  
% 15.33/2.51  --bmc1_incremental                      false
% 15.33/2.51  --bmc1_axioms                           reachable_all
% 15.33/2.51  --bmc1_min_bound                        0
% 15.33/2.51  --bmc1_max_bound                        -1
% 15.33/2.51  --bmc1_max_bound_default                -1
% 15.33/2.51  --bmc1_symbol_reachability              true
% 15.33/2.51  --bmc1_property_lemmas                  false
% 15.33/2.51  --bmc1_k_induction                      false
% 15.33/2.51  --bmc1_non_equiv_states                 false
% 15.33/2.51  --bmc1_deadlock                         false
% 15.33/2.51  --bmc1_ucm                              false
% 15.33/2.51  --bmc1_add_unsat_core                   none
% 15.33/2.51  --bmc1_unsat_core_children              false
% 15.33/2.51  --bmc1_unsat_core_extrapolate_axioms    false
% 15.33/2.51  --bmc1_out_stat                         full
% 15.33/2.51  --bmc1_ground_init                      false
% 15.33/2.51  --bmc1_pre_inst_next_state              false
% 15.33/2.51  --bmc1_pre_inst_state                   false
% 15.33/2.51  --bmc1_pre_inst_reach_state             false
% 15.33/2.51  --bmc1_out_unsat_core                   false
% 15.33/2.51  --bmc1_aig_witness_out                  false
% 15.33/2.51  --bmc1_verbose                          false
% 15.33/2.51  --bmc1_dump_clauses_tptp                false
% 15.33/2.51  --bmc1_dump_unsat_core_tptp             false
% 15.33/2.51  --bmc1_dump_file                        -
% 15.33/2.51  --bmc1_ucm_expand_uc_limit              128
% 15.33/2.51  --bmc1_ucm_n_expand_iterations          6
% 15.33/2.51  --bmc1_ucm_extend_mode                  1
% 15.33/2.51  --bmc1_ucm_init_mode                    2
% 15.33/2.51  --bmc1_ucm_cone_mode                    none
% 15.33/2.51  --bmc1_ucm_reduced_relation_type        0
% 15.33/2.51  --bmc1_ucm_relax_model                  4
% 15.33/2.51  --bmc1_ucm_full_tr_after_sat            true
% 15.33/2.51  --bmc1_ucm_expand_neg_assumptions       false
% 15.33/2.51  --bmc1_ucm_layered_model                none
% 15.33/2.51  --bmc1_ucm_max_lemma_size               10
% 15.33/2.51  
% 15.33/2.51  ------ AIG Options
% 15.33/2.51  
% 15.33/2.51  --aig_mode                              false
% 15.33/2.51  
% 15.33/2.51  ------ Instantiation Options
% 15.33/2.51  
% 15.33/2.51  --instantiation_flag                    true
% 15.33/2.51  --inst_sos_flag                         false
% 15.33/2.51  --inst_sos_phase                        true
% 15.33/2.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.33/2.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.33/2.51  --inst_lit_sel_side                     num_symb
% 15.33/2.51  --inst_solver_per_active                1400
% 15.33/2.51  --inst_solver_calls_frac                1.
% 15.33/2.51  --inst_passive_queue_type               priority_queues
% 15.33/2.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.33/2.51  --inst_passive_queues_freq              [25;2]
% 15.33/2.51  --inst_dismatching                      true
% 15.33/2.51  --inst_eager_unprocessed_to_passive     true
% 15.33/2.51  --inst_prop_sim_given                   true
% 15.33/2.51  --inst_prop_sim_new                     false
% 15.33/2.51  --inst_subs_new                         false
% 15.33/2.51  --inst_eq_res_simp                      false
% 15.33/2.51  --inst_subs_given                       false
% 15.33/2.51  --inst_orphan_elimination               true
% 15.33/2.51  --inst_learning_loop_flag               true
% 15.33/2.51  --inst_learning_start                   3000
% 15.33/2.51  --inst_learning_factor                  2
% 15.33/2.51  --inst_start_prop_sim_after_learn       3
% 15.33/2.51  --inst_sel_renew                        solver
% 15.33/2.51  --inst_lit_activity_flag                true
% 15.33/2.51  --inst_restr_to_given                   false
% 15.33/2.51  --inst_activity_threshold               500
% 15.33/2.51  --inst_out_proof                        true
% 15.33/2.51  
% 15.33/2.51  ------ Resolution Options
% 15.33/2.51  
% 15.33/2.51  --resolution_flag                       true
% 15.33/2.51  --res_lit_sel                           adaptive
% 15.33/2.51  --res_lit_sel_side                      none
% 15.33/2.51  --res_ordering                          kbo
% 15.33/2.51  --res_to_prop_solver                    active
% 15.33/2.51  --res_prop_simpl_new                    false
% 15.33/2.51  --res_prop_simpl_given                  true
% 15.33/2.51  --res_passive_queue_type                priority_queues
% 15.33/2.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.33/2.51  --res_passive_queues_freq               [15;5]
% 15.33/2.51  --res_forward_subs                      full
% 15.33/2.51  --res_backward_subs                     full
% 15.33/2.51  --res_forward_subs_resolution           true
% 15.33/2.51  --res_backward_subs_resolution          true
% 15.33/2.51  --res_orphan_elimination                true
% 15.33/2.51  --res_time_limit                        2.
% 15.33/2.51  --res_out_proof                         true
% 15.33/2.51  
% 15.33/2.51  ------ Superposition Options
% 15.33/2.51  
% 15.33/2.51  --superposition_flag                    true
% 15.33/2.51  --sup_passive_queue_type                priority_queues
% 15.33/2.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.33/2.51  --sup_passive_queues_freq               [8;1;4]
% 15.33/2.51  --demod_completeness_check              fast
% 15.33/2.51  --demod_use_ground                      true
% 15.33/2.51  --sup_to_prop_solver                    passive
% 15.33/2.51  --sup_prop_simpl_new                    true
% 15.33/2.51  --sup_prop_simpl_given                  true
% 15.33/2.51  --sup_fun_splitting                     false
% 15.33/2.51  --sup_smt_interval                      50000
% 15.33/2.51  
% 15.33/2.51  ------ Superposition Simplification Setup
% 15.33/2.51  
% 15.33/2.51  --sup_indices_passive                   []
% 15.33/2.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.33/2.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.33/2.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.33/2.51  --sup_full_triv                         [TrivRules;PropSubs]
% 15.33/2.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.33/2.51  --sup_full_bw                           [BwDemod]
% 15.33/2.51  --sup_immed_triv                        [TrivRules]
% 15.33/2.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.33/2.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.33/2.51  --sup_immed_bw_main                     []
% 15.33/2.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.33/2.51  --sup_input_triv                        [Unflattening;TrivRules]
% 15.33/2.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.33/2.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.33/2.51  
% 15.33/2.51  ------ Combination Options
% 15.33/2.51  
% 15.33/2.51  --comb_res_mult                         3
% 15.33/2.51  --comb_sup_mult                         2
% 15.33/2.51  --comb_inst_mult                        10
% 15.33/2.51  
% 15.33/2.51  ------ Debug Options
% 15.33/2.51  
% 15.33/2.51  --dbg_backtrace                         false
% 15.33/2.51  --dbg_dump_prop_clauses                 false
% 15.33/2.51  --dbg_dump_prop_clauses_file            -
% 15.33/2.51  --dbg_out_stat                          false
% 15.33/2.51  ------ Parsing...
% 15.33/2.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.33/2.51  
% 15.33/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 15.33/2.51  
% 15.33/2.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.33/2.51  
% 15.33/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.33/2.51  ------ Proving...
% 15.33/2.51  ------ Problem Properties 
% 15.33/2.51  
% 15.33/2.51  
% 15.33/2.51  clauses                                 10
% 15.33/2.51  conjectures                             3
% 15.33/2.51  EPR                                     0
% 15.33/2.51  Horn                                    10
% 15.33/2.51  unary                                   4
% 15.33/2.51  binary                                  1
% 15.33/2.51  lits                                    22
% 15.33/2.51  lits eq                                 7
% 15.33/2.51  fd_pure                                 0
% 15.33/2.51  fd_pseudo                               0
% 15.33/2.51  fd_cond                                 0
% 15.33/2.51  fd_pseudo_cond                          0
% 15.33/2.51  AC symbols                              0
% 15.33/2.51  
% 15.33/2.51  ------ Schedule dynamic 5 is on 
% 15.33/2.51  
% 15.33/2.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.33/2.51  
% 15.33/2.51  
% 15.33/2.51  ------ 
% 15.33/2.51  Current options:
% 15.33/2.51  ------ 
% 15.33/2.51  
% 15.33/2.51  ------ Input Options
% 15.33/2.51  
% 15.33/2.51  --out_options                           all
% 15.33/2.51  --tptp_safe_out                         true
% 15.33/2.51  --problem_path                          ""
% 15.33/2.51  --include_path                          ""
% 15.33/2.51  --clausifier                            res/vclausify_rel
% 15.33/2.51  --clausifier_options                    --mode clausify
% 15.33/2.51  --stdin                                 false
% 15.33/2.51  --stats_out                             all
% 15.33/2.51  
% 15.33/2.51  ------ General Options
% 15.33/2.51  
% 15.33/2.51  --fof                                   false
% 15.33/2.51  --time_out_real                         305.
% 15.33/2.51  --time_out_virtual                      -1.
% 15.33/2.51  --symbol_type_check                     false
% 15.33/2.51  --clausify_out                          false
% 15.33/2.51  --sig_cnt_out                           false
% 15.33/2.51  --trig_cnt_out                          false
% 15.33/2.51  --trig_cnt_out_tolerance                1.
% 15.33/2.51  --trig_cnt_out_sk_spl                   false
% 15.33/2.51  --abstr_cl_out                          false
% 15.33/2.51  
% 15.33/2.51  ------ Global Options
% 15.33/2.51  
% 15.33/2.51  --schedule                              default
% 15.33/2.51  --add_important_lit                     false
% 15.33/2.51  --prop_solver_per_cl                    1000
% 15.33/2.51  --min_unsat_core                        false
% 15.33/2.51  --soft_assumptions                      false
% 15.33/2.51  --soft_lemma_size                       3
% 15.33/2.51  --prop_impl_unit_size                   0
% 15.33/2.51  --prop_impl_unit                        []
% 15.33/2.51  --share_sel_clauses                     true
% 15.33/2.51  --reset_solvers                         false
% 15.33/2.51  --bc_imp_inh                            [conj_cone]
% 15.33/2.51  --conj_cone_tolerance                   3.
% 15.33/2.51  --extra_neg_conj                        none
% 15.33/2.51  --large_theory_mode                     true
% 15.33/2.51  --prolific_symb_bound                   200
% 15.33/2.51  --lt_threshold                          2000
% 15.33/2.51  --clause_weak_htbl                      true
% 15.33/2.51  --gc_record_bc_elim                     false
% 15.33/2.51  
% 15.33/2.51  ------ Preprocessing Options
% 15.33/2.51  
% 15.33/2.51  --preprocessing_flag                    true
% 15.33/2.51  --time_out_prep_mult                    0.1
% 15.33/2.51  --splitting_mode                        input
% 15.33/2.51  --splitting_grd                         true
% 15.33/2.51  --splitting_cvd                         false
% 15.33/2.51  --splitting_cvd_svl                     false
% 15.33/2.51  --splitting_nvd                         32
% 15.33/2.51  --sub_typing                            true
% 15.33/2.51  --prep_gs_sim                           true
% 15.33/2.51  --prep_unflatten                        true
% 15.33/2.51  --prep_res_sim                          true
% 15.33/2.51  --prep_upred                            true
% 15.33/2.51  --prep_sem_filter                       exhaustive
% 15.33/2.51  --prep_sem_filter_out                   false
% 15.33/2.51  --pred_elim                             true
% 15.33/2.51  --res_sim_input                         true
% 15.33/2.51  --eq_ax_congr_red                       true
% 15.33/2.51  --pure_diseq_elim                       true
% 15.33/2.51  --brand_transform                       false
% 15.33/2.51  --non_eq_to_eq                          false
% 15.33/2.51  --prep_def_merge                        true
% 15.33/2.51  --prep_def_merge_prop_impl              false
% 15.33/2.51  --prep_def_merge_mbd                    true
% 15.33/2.51  --prep_def_merge_tr_red                 false
% 15.33/2.51  --prep_def_merge_tr_cl                  false
% 15.33/2.51  --smt_preprocessing                     true
% 15.33/2.51  --smt_ac_axioms                         fast
% 15.33/2.51  --preprocessed_out                      false
% 15.33/2.51  --preprocessed_stats                    false
% 15.33/2.51  
% 15.33/2.51  ------ Abstraction refinement Options
% 15.33/2.51  
% 15.33/2.51  --abstr_ref                             []
% 15.33/2.51  --abstr_ref_prep                        false
% 15.33/2.51  --abstr_ref_until_sat                   false
% 15.33/2.51  --abstr_ref_sig_restrict                funpre
% 15.33/2.51  --abstr_ref_af_restrict_to_split_sk     false
% 15.33/2.51  --abstr_ref_under                       []
% 15.33/2.51  
% 15.33/2.51  ------ SAT Options
% 15.33/2.51  
% 15.33/2.51  --sat_mode                              false
% 15.33/2.51  --sat_fm_restart_options                ""
% 15.33/2.51  --sat_gr_def                            false
% 15.33/2.51  --sat_epr_types                         true
% 15.33/2.51  --sat_non_cyclic_types                  false
% 15.33/2.51  --sat_finite_models                     false
% 15.33/2.51  --sat_fm_lemmas                         false
% 15.33/2.51  --sat_fm_prep                           false
% 15.33/2.51  --sat_fm_uc_incr                        true
% 15.33/2.51  --sat_out_model                         small
% 15.33/2.51  --sat_out_clauses                       false
% 15.33/2.51  
% 15.33/2.51  ------ QBF Options
% 15.33/2.51  
% 15.33/2.51  --qbf_mode                              false
% 15.33/2.51  --qbf_elim_univ                         false
% 15.33/2.51  --qbf_dom_inst                          none
% 15.33/2.51  --qbf_dom_pre_inst                      false
% 15.33/2.51  --qbf_sk_in                             false
% 15.33/2.51  --qbf_pred_elim                         true
% 15.33/2.51  --qbf_split                             512
% 15.33/2.51  
% 15.33/2.51  ------ BMC1 Options
% 15.33/2.51  
% 15.33/2.51  --bmc1_incremental                      false
% 15.33/2.51  --bmc1_axioms                           reachable_all
% 15.33/2.51  --bmc1_min_bound                        0
% 15.33/2.51  --bmc1_max_bound                        -1
% 15.33/2.51  --bmc1_max_bound_default                -1
% 15.33/2.51  --bmc1_symbol_reachability              true
% 15.33/2.51  --bmc1_property_lemmas                  false
% 15.33/2.51  --bmc1_k_induction                      false
% 15.33/2.51  --bmc1_non_equiv_states                 false
% 15.33/2.51  --bmc1_deadlock                         false
% 15.33/2.51  --bmc1_ucm                              false
% 15.33/2.51  --bmc1_add_unsat_core                   none
% 15.33/2.51  --bmc1_unsat_core_children              false
% 15.33/2.51  --bmc1_unsat_core_extrapolate_axioms    false
% 15.33/2.51  --bmc1_out_stat                         full
% 15.33/2.51  --bmc1_ground_init                      false
% 15.33/2.51  --bmc1_pre_inst_next_state              false
% 15.33/2.51  --bmc1_pre_inst_state                   false
% 15.33/2.51  --bmc1_pre_inst_reach_state             false
% 15.33/2.51  --bmc1_out_unsat_core                   false
% 15.33/2.51  --bmc1_aig_witness_out                  false
% 15.33/2.51  --bmc1_verbose                          false
% 15.33/2.51  --bmc1_dump_clauses_tptp                false
% 15.33/2.51  --bmc1_dump_unsat_core_tptp             false
% 15.33/2.51  --bmc1_dump_file                        -
% 15.33/2.51  --bmc1_ucm_expand_uc_limit              128
% 15.33/2.51  --bmc1_ucm_n_expand_iterations          6
% 15.33/2.51  --bmc1_ucm_extend_mode                  1
% 15.33/2.51  --bmc1_ucm_init_mode                    2
% 15.33/2.51  --bmc1_ucm_cone_mode                    none
% 15.33/2.51  --bmc1_ucm_reduced_relation_type        0
% 15.33/2.51  --bmc1_ucm_relax_model                  4
% 15.33/2.51  --bmc1_ucm_full_tr_after_sat            true
% 15.33/2.51  --bmc1_ucm_expand_neg_assumptions       false
% 15.33/2.51  --bmc1_ucm_layered_model                none
% 15.33/2.51  --bmc1_ucm_max_lemma_size               10
% 15.33/2.51  
% 15.33/2.51  ------ AIG Options
% 15.33/2.51  
% 15.33/2.51  --aig_mode                              false
% 15.33/2.51  
% 15.33/2.51  ------ Instantiation Options
% 15.33/2.51  
% 15.33/2.51  --instantiation_flag                    true
% 15.33/2.51  --inst_sos_flag                         false
% 15.33/2.51  --inst_sos_phase                        true
% 15.33/2.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.33/2.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.33/2.51  --inst_lit_sel_side                     none
% 15.33/2.51  --inst_solver_per_active                1400
% 15.33/2.51  --inst_solver_calls_frac                1.
% 15.33/2.51  --inst_passive_queue_type               priority_queues
% 15.33/2.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.33/2.51  --inst_passive_queues_freq              [25;2]
% 15.33/2.51  --inst_dismatching                      true
% 15.33/2.51  --inst_eager_unprocessed_to_passive     true
% 15.33/2.51  --inst_prop_sim_given                   true
% 15.33/2.51  --inst_prop_sim_new                     false
% 15.33/2.51  --inst_subs_new                         false
% 15.33/2.51  --inst_eq_res_simp                      false
% 15.33/2.51  --inst_subs_given                       false
% 15.33/2.51  --inst_orphan_elimination               true
% 15.33/2.51  --inst_learning_loop_flag               true
% 15.33/2.51  --inst_learning_start                   3000
% 15.33/2.51  --inst_learning_factor                  2
% 15.33/2.51  --inst_start_prop_sim_after_learn       3
% 15.33/2.51  --inst_sel_renew                        solver
% 15.33/2.51  --inst_lit_activity_flag                true
% 15.33/2.51  --inst_restr_to_given                   false
% 15.33/2.51  --inst_activity_threshold               500
% 15.33/2.51  --inst_out_proof                        true
% 15.33/2.51  
% 15.33/2.51  ------ Resolution Options
% 15.33/2.51  
% 15.33/2.51  --resolution_flag                       false
% 15.33/2.51  --res_lit_sel                           adaptive
% 15.33/2.51  --res_lit_sel_side                      none
% 15.33/2.51  --res_ordering                          kbo
% 15.33/2.51  --res_to_prop_solver                    active
% 15.33/2.51  --res_prop_simpl_new                    false
% 15.33/2.51  --res_prop_simpl_given                  true
% 15.33/2.51  --res_passive_queue_type                priority_queues
% 15.33/2.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.33/2.51  --res_passive_queues_freq               [15;5]
% 15.33/2.51  --res_forward_subs                      full
% 15.33/2.51  --res_backward_subs                     full
% 15.33/2.51  --res_forward_subs_resolution           true
% 15.33/2.51  --res_backward_subs_resolution          true
% 15.33/2.51  --res_orphan_elimination                true
% 15.33/2.51  --res_time_limit                        2.
% 15.33/2.51  --res_out_proof                         true
% 15.33/2.51  
% 15.33/2.51  ------ Superposition Options
% 15.33/2.51  
% 15.33/2.51  --superposition_flag                    true
% 15.33/2.51  --sup_passive_queue_type                priority_queues
% 15.33/2.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.33/2.51  --sup_passive_queues_freq               [8;1;4]
% 15.33/2.51  --demod_completeness_check              fast
% 15.33/2.51  --demod_use_ground                      true
% 15.33/2.51  --sup_to_prop_solver                    passive
% 15.33/2.51  --sup_prop_simpl_new                    true
% 15.33/2.51  --sup_prop_simpl_given                  true
% 15.33/2.51  --sup_fun_splitting                     false
% 15.33/2.51  --sup_smt_interval                      50000
% 15.33/2.51  
% 15.33/2.51  ------ Superposition Simplification Setup
% 15.33/2.51  
% 15.33/2.51  --sup_indices_passive                   []
% 15.33/2.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.33/2.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.33/2.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.33/2.51  --sup_full_triv                         [TrivRules;PropSubs]
% 15.33/2.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.33/2.51  --sup_full_bw                           [BwDemod]
% 15.33/2.51  --sup_immed_triv                        [TrivRules]
% 15.33/2.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.33/2.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.33/2.51  --sup_immed_bw_main                     []
% 15.33/2.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.33/2.51  --sup_input_triv                        [Unflattening;TrivRules]
% 15.33/2.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.33/2.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.33/2.51  
% 15.33/2.51  ------ Combination Options
% 15.33/2.51  
% 15.33/2.51  --comb_res_mult                         3
% 15.33/2.51  --comb_sup_mult                         2
% 15.33/2.51  --comb_inst_mult                        10
% 15.33/2.51  
% 15.33/2.51  ------ Debug Options
% 15.33/2.51  
% 15.33/2.51  --dbg_backtrace                         false
% 15.33/2.51  --dbg_dump_prop_clauses                 false
% 15.33/2.51  --dbg_dump_prop_clauses_file            -
% 15.33/2.51  --dbg_out_stat                          false
% 15.33/2.51  
% 15.33/2.51  
% 15.33/2.51  
% 15.33/2.51  
% 15.33/2.51  ------ Proving...
% 15.33/2.51  
% 15.33/2.51  
% 15.33/2.51  % SZS status Theorem for theBenchmark.p
% 15.33/2.51  
% 15.33/2.51  % SZS output start CNFRefutation for theBenchmark.p
% 15.33/2.51  
% 15.33/2.51  fof(f7,conjecture,(
% 15.33/2.51    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)))))))),
% 15.33/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.33/2.51  
% 15.33/2.51  fof(f8,negated_conjecture,(
% 15.33/2.51    ~! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)))))))),
% 15.33/2.51    inference(negated_conjecture,[],[f7])).
% 15.33/2.51  
% 15.33/2.51  fof(f21,plain,(
% 15.33/2.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,X1,X2)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)))),
% 15.33/2.51    inference(ennf_transformation,[],[f8])).
% 15.33/2.51  
% 15.33/2.51  fof(f22,plain,(
% 15.33/2.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0))),
% 15.33/2.51    inference(flattening,[],[f21])).
% 15.33/2.51  
% 15.33/2.51  fof(f43,plain,(
% 15.33/2.51    ( ! [X2,X0,X1] : (? [X3] : (~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,k2_lattices(X0,X1,sK10),k2_lattices(X0,X2,sK10)) & r1_lattices(X0,X1,X2) & m1_subset_1(sK10,u1_struct_0(X0)))) )),
% 15.33/2.51    introduced(choice_axiom,[])).
% 15.33/2.51  
% 15.33/2.51  fof(f42,plain,(
% 15.33/2.51    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,sK9,X3)) & r1_lattices(X0,X1,sK9) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK9,u1_struct_0(X0)))) )),
% 15.33/2.51    introduced(choice_axiom,[])).
% 15.33/2.51  
% 15.33/2.51  fof(f41,plain,(
% 15.33/2.51    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~r1_lattices(X0,k2_lattices(X0,sK8,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,sK8,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK8,u1_struct_0(X0)))) )),
% 15.33/2.51    introduced(choice_axiom,[])).
% 15.33/2.51  
% 15.33/2.51  fof(f40,plain,(
% 15.33/2.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_lattices(sK7,k2_lattices(sK7,X1,X3),k2_lattices(sK7,X2,X3)) & r1_lattices(sK7,X1,X2) & m1_subset_1(X3,u1_struct_0(sK7))) & m1_subset_1(X2,u1_struct_0(sK7))) & m1_subset_1(X1,u1_struct_0(sK7))) & l3_lattices(sK7) & v9_lattices(sK7) & v8_lattices(sK7) & v7_lattices(sK7) & ~v2_struct_0(sK7))),
% 15.33/2.51    introduced(choice_axiom,[])).
% 15.33/2.51  
% 15.33/2.51  fof(f44,plain,(
% 15.33/2.51    (((~r1_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10)) & r1_lattices(sK7,sK8,sK9) & m1_subset_1(sK10,u1_struct_0(sK7))) & m1_subset_1(sK9,u1_struct_0(sK7))) & m1_subset_1(sK8,u1_struct_0(sK7))) & l3_lattices(sK7) & v9_lattices(sK7) & v8_lattices(sK7) & v7_lattices(sK7) & ~v2_struct_0(sK7)),
% 15.33/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f22,f43,f42,f41,f40])).
% 15.33/2.51  
% 15.33/2.51  fof(f69,plain,(
% 15.33/2.51    m1_subset_1(sK10,u1_struct_0(sK7))),
% 15.33/2.51    inference(cnf_transformation,[],[f44])).
% 15.33/2.51  
% 15.33/2.51  fof(f68,plain,(
% 15.33/2.51    m1_subset_1(sK9,u1_struct_0(sK7))),
% 15.33/2.51    inference(cnf_transformation,[],[f44])).
% 15.33/2.51  
% 15.33/2.51  fof(f5,axiom,(
% 15.33/2.51    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 15.33/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.33/2.51  
% 15.33/2.51  fof(f9,plain,(
% 15.33/2.51    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 15.33/2.51    inference(pure_predicate_removal,[],[f5])).
% 15.33/2.51  
% 15.33/2.51  fof(f18,plain,(
% 15.33/2.51    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 15.33/2.51    inference(ennf_transformation,[],[f9])).
% 15.33/2.51  
% 15.33/2.51  fof(f59,plain,(
% 15.33/2.51    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 15.33/2.51    inference(cnf_transformation,[],[f18])).
% 15.33/2.51  
% 15.33/2.51  fof(f1,axiom,(
% 15.33/2.51    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v7_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3))))))),
% 15.33/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.33/2.51  
% 15.33/2.51  fof(f10,plain,(
% 15.33/2.51    ! [X0] : ((v7_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 15.33/2.51    inference(ennf_transformation,[],[f1])).
% 15.33/2.51  
% 15.33/2.51  fof(f11,plain,(
% 15.33/2.51    ! [X0] : ((v7_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 15.33/2.51    inference(flattening,[],[f10])).
% 15.33/2.51  
% 15.33/2.51  fof(f23,plain,(
% 15.33/2.51    ! [X0] : (((v7_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v7_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 15.33/2.51    inference(nnf_transformation,[],[f11])).
% 15.33/2.51  
% 15.33/2.51  fof(f24,plain,(
% 15.33/2.51    ! [X0] : (((v7_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v7_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 15.33/2.51    inference(rectify,[],[f23])).
% 15.33/2.51  
% 15.33/2.51  fof(f27,plain,(
% 15.33/2.51    ( ! [X2,X1] : (! [X0] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) => (k2_lattices(X0,X1,k2_lattices(X0,X2,sK2(X0))) != k2_lattices(X0,k2_lattices(X0,X1,X2),sK2(X0)) & m1_subset_1(sK2(X0),u1_struct_0(X0))))) )),
% 15.33/2.51    introduced(choice_axiom,[])).
% 15.33/2.51  
% 15.33/2.51  fof(f26,plain,(
% 15.33/2.51    ( ! [X1] : (! [X0] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,sK1(X0),X3)) != k2_lattices(X0,k2_lattices(X0,X1,sK1(X0)),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK1(X0),u1_struct_0(X0))))) )),
% 15.33/2.51    introduced(choice_axiom,[])).
% 15.33/2.51  
% 15.33/2.51  fof(f25,plain,(
% 15.33/2.51    ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k2_lattices(X0,k2_lattices(X0,sK0(X0),X2),X3) != k2_lattices(X0,sK0(X0),k2_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0))))),
% 15.33/2.51    introduced(choice_axiom,[])).
% 15.33/2.51  
% 15.33/2.51  fof(f28,plain,(
% 15.33/2.51    ! [X0] : (((v7_lattices(X0) | (((k2_lattices(X0,k2_lattices(X0,sK0(X0),sK1(X0)),sK2(X0)) != k2_lattices(X0,sK0(X0),k2_lattices(X0,sK1(X0),sK2(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))) & m1_subset_1(sK1(X0),u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v7_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 15.33/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).
% 15.33/2.51  
% 15.33/2.51  fof(f45,plain,(
% 15.33/2.51    ( ! [X6,X4,X0,X5] : (k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v7_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 15.33/2.51    inference(cnf_transformation,[],[f28])).
% 15.33/2.51  
% 15.33/2.51  fof(f62,plain,(
% 15.33/2.51    ~v2_struct_0(sK7)),
% 15.33/2.51    inference(cnf_transformation,[],[f44])).
% 15.33/2.51  
% 15.33/2.51  fof(f66,plain,(
% 15.33/2.51    l3_lattices(sK7)),
% 15.33/2.51    inference(cnf_transformation,[],[f44])).
% 15.33/2.51  
% 15.33/2.51  fof(f63,plain,(
% 15.33/2.51    v7_lattices(sK7)),
% 15.33/2.51    inference(cnf_transformation,[],[f44])).
% 15.33/2.51  
% 15.33/2.51  fof(f4,axiom,(
% 15.33/2.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 15.33/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.33/2.51  
% 15.33/2.51  fof(f16,plain,(
% 15.33/2.51    ! [X0,X1,X2] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)))),
% 15.33/2.51    inference(ennf_transformation,[],[f4])).
% 15.33/2.51  
% 15.33/2.51  fof(f17,plain,(
% 15.33/2.51    ! [X0,X1,X2] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 15.33/2.51    inference(flattening,[],[f16])).
% 15.33/2.51  
% 15.33/2.51  fof(f58,plain,(
% 15.33/2.51    ( ! [X2,X0,X1] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 15.33/2.51    inference(cnf_transformation,[],[f17])).
% 15.33/2.51  
% 15.33/2.51  fof(f3,axiom,(
% 15.33/2.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 15.33/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.33/2.51  
% 15.33/2.51  fof(f14,plain,(
% 15.33/2.51    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 15.33/2.51    inference(ennf_transformation,[],[f3])).
% 15.33/2.51  
% 15.33/2.51  fof(f15,plain,(
% 15.33/2.51    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.33/2.51    inference(flattening,[],[f14])).
% 15.33/2.51  
% 15.33/2.51  fof(f34,plain,(
% 15.33/2.51    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.33/2.51    inference(nnf_transformation,[],[f15])).
% 15.33/2.51  
% 15.33/2.51  fof(f35,plain,(
% 15.33/2.51    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.33/2.51    inference(rectify,[],[f34])).
% 15.33/2.51  
% 15.33/2.51  fof(f37,plain,(
% 15.33/2.51    ( ! [X1] : (! [X0] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,X1,k1_lattices(X0,X1,sK6(X0))) != X1 & m1_subset_1(sK6(X0),u1_struct_0(X0))))) )),
% 15.33/2.51    introduced(choice_axiom,[])).
% 15.33/2.51  
% 15.33/2.51  fof(f36,plain,(
% 15.33/2.51    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),X2)) != sK5(X0) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 15.33/2.51    introduced(choice_axiom,[])).
% 15.33/2.51  
% 15.33/2.51  fof(f38,plain,(
% 15.33/2.51    ! [X0] : (((v9_lattices(X0) | ((k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),sK6(X0))) != sK5(X0) & m1_subset_1(sK6(X0),u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.33/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f35,f37,f36])).
% 15.33/2.51  
% 15.33/2.51  fof(f54,plain,(
% 15.33/2.51    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v9_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.33/2.51    inference(cnf_transformation,[],[f38])).
% 15.33/2.51  
% 15.33/2.51  fof(f65,plain,(
% 15.33/2.51    v9_lattices(sK7)),
% 15.33/2.51    inference(cnf_transformation,[],[f44])).
% 15.33/2.51  
% 15.33/2.51  fof(f2,axiom,(
% 15.33/2.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 15.33/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.33/2.51  
% 15.33/2.51  fof(f12,plain,(
% 15.33/2.51    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 15.33/2.51    inference(ennf_transformation,[],[f2])).
% 15.33/2.51  
% 15.33/2.51  fof(f13,plain,(
% 15.33/2.51    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.33/2.51    inference(flattening,[],[f12])).
% 15.33/2.51  
% 15.33/2.51  fof(f29,plain,(
% 15.33/2.51    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.33/2.51    inference(nnf_transformation,[],[f13])).
% 15.33/2.51  
% 15.33/2.51  fof(f30,plain,(
% 15.33/2.51    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.33/2.51    inference(rectify,[],[f29])).
% 15.33/2.51  
% 15.33/2.51  fof(f32,plain,(
% 15.33/2.51    ( ! [X1] : (! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (k1_lattices(X0,k2_lattices(X0,X1,sK4(X0)),sK4(X0)) != sK4(X0) & m1_subset_1(sK4(X0),u1_struct_0(X0))))) )),
% 15.33/2.51    introduced(choice_axiom,[])).
% 15.33/2.51  
% 15.33/2.51  fof(f31,plain,(
% 15.33/2.51    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 15.33/2.51    introduced(choice_axiom,[])).
% 15.33/2.51  
% 15.33/2.51  fof(f33,plain,(
% 15.33/2.51    ! [X0] : (((v8_lattices(X0) | ((k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0)) != sK4(X0) & m1_subset_1(sK4(X0),u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 15.33/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f30,f32,f31])).
% 15.33/2.51  
% 15.33/2.51  fof(f50,plain,(
% 15.33/2.51    ( ! [X4,X0,X3] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v8_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 15.33/2.51    inference(cnf_transformation,[],[f33])).
% 15.33/2.51  
% 15.33/2.51  fof(f64,plain,(
% 15.33/2.51    v8_lattices(sK7)),
% 15.33/2.51    inference(cnf_transformation,[],[f44])).
% 15.33/2.51  
% 15.33/2.51  fof(f67,plain,(
% 15.33/2.51    m1_subset_1(sK8,u1_struct_0(sK7))),
% 15.33/2.51    inference(cnf_transformation,[],[f44])).
% 15.33/2.51  
% 15.33/2.51  fof(f6,axiom,(
% 15.33/2.51    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 15.33/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.33/2.51  
% 15.33/2.51  fof(f19,plain,(
% 15.33/2.51    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 15.33/2.51    inference(ennf_transformation,[],[f6])).
% 15.33/2.51  
% 15.33/2.51  fof(f20,plain,(
% 15.33/2.51    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 15.33/2.51    inference(flattening,[],[f19])).
% 15.33/2.51  
% 15.33/2.51  fof(f39,plain,(
% 15.33/2.51    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 15.33/2.51    inference(nnf_transformation,[],[f20])).
% 15.33/2.51  
% 15.33/2.51  fof(f60,plain,(
% 15.33/2.51    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 15.33/2.51    inference(cnf_transformation,[],[f39])).
% 15.33/2.51  
% 15.33/2.51  fof(f70,plain,(
% 15.33/2.51    r1_lattices(sK7,sK8,sK9)),
% 15.33/2.51    inference(cnf_transformation,[],[f44])).
% 15.33/2.51  
% 15.33/2.51  fof(f61,plain,(
% 15.33/2.51    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 15.33/2.51    inference(cnf_transformation,[],[f39])).
% 15.33/2.51  
% 15.33/2.51  fof(f71,plain,(
% 15.33/2.51    ~r1_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10))),
% 15.33/2.51    inference(cnf_transformation,[],[f44])).
% 15.33/2.51  
% 15.33/2.51  cnf(c_19,negated_conjecture,
% 15.33/2.51      ( m1_subset_1(sK10,u1_struct_0(sK7)) ),
% 15.33/2.51      inference(cnf_transformation,[],[f69]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_1026,negated_conjecture,
% 15.33/2.51      ( m1_subset_1(sK10,u1_struct_0(sK7)) ),
% 15.33/2.51      inference(subtyping,[status(esa)],[c_19]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_1171,plain,
% 15.33/2.51      ( m1_subset_1(sK10,u1_struct_0(sK7)) = iProver_top ),
% 15.33/2.51      inference(predicate_to_equality,[status(thm)],[c_1026]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_20,negated_conjecture,
% 15.33/2.51      ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
% 15.33/2.51      inference(cnf_transformation,[],[f68]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_1025,negated_conjecture,
% 15.33/2.51      ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
% 15.33/2.51      inference(subtyping,[status(esa)],[c_20]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_1172,plain,
% 15.33/2.51      ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
% 15.33/2.51      inference(predicate_to_equality,[status(thm)],[c_1025]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_14,plain,
% 15.33/2.51      ( ~ l3_lattices(X0) | l1_lattices(X0) ),
% 15.33/2.51      inference(cnf_transformation,[],[f59]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_4,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.33/2.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.33/2.51      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 15.33/2.51      | v2_struct_0(X1)
% 15.33/2.51      | ~ l1_lattices(X1)
% 15.33/2.51      | ~ v7_lattices(X1)
% 15.33/2.51      | k2_lattices(X1,k2_lattices(X1,X3,X2),X0) = k2_lattices(X1,X3,k2_lattices(X1,X2,X0)) ),
% 15.33/2.51      inference(cnf_transformation,[],[f45]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_352,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.33/2.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.33/2.51      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 15.33/2.51      | ~ l3_lattices(X4)
% 15.33/2.51      | v2_struct_0(X1)
% 15.33/2.51      | ~ v7_lattices(X1)
% 15.33/2.51      | X1 != X4
% 15.33/2.51      | k2_lattices(X1,X3,k2_lattices(X1,X2,X0)) = k2_lattices(X1,k2_lattices(X1,X3,X2),X0) ),
% 15.33/2.51      inference(resolution_lifted,[status(thm)],[c_14,c_4]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_353,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.33/2.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.33/2.51      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 15.33/2.51      | ~ l3_lattices(X1)
% 15.33/2.51      | v2_struct_0(X1)
% 15.33/2.51      | ~ v7_lattices(X1)
% 15.33/2.51      | k2_lattices(X1,X3,k2_lattices(X1,X2,X0)) = k2_lattices(X1,k2_lattices(X1,X3,X2),X0) ),
% 15.33/2.51      inference(unflattening,[status(thm)],[c_352]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_26,negated_conjecture,
% 15.33/2.51      ( ~ v2_struct_0(sK7) ),
% 15.33/2.51      inference(cnf_transformation,[],[f62]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_869,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.33/2.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.33/2.51      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 15.33/2.51      | ~ l3_lattices(X1)
% 15.33/2.51      | ~ v7_lattices(X1)
% 15.33/2.51      | k2_lattices(X1,X3,k2_lattices(X1,X2,X0)) = k2_lattices(X1,k2_lattices(X1,X3,X2),X0)
% 15.33/2.51      | sK7 != X1 ),
% 15.33/2.51      inference(resolution_lifted,[status(thm)],[c_353,c_26]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_870,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 15.33/2.51      | ~ l3_lattices(sK7)
% 15.33/2.51      | ~ v7_lattices(sK7)
% 15.33/2.51      | k2_lattices(sK7,X2,k2_lattices(sK7,X0,X1)) = k2_lattices(sK7,k2_lattices(sK7,X2,X0),X1) ),
% 15.33/2.51      inference(unflattening,[status(thm)],[c_869]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_22,negated_conjecture,
% 15.33/2.51      ( l3_lattices(sK7) ),
% 15.33/2.51      inference(cnf_transformation,[],[f66]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_25,negated_conjecture,
% 15.33/2.51      ( v7_lattices(sK7) ),
% 15.33/2.51      inference(cnf_transformation,[],[f63]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_793,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.33/2.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.33/2.51      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 15.33/2.51      | ~ l3_lattices(X1)
% 15.33/2.51      | v2_struct_0(X1)
% 15.33/2.51      | k2_lattices(X1,X3,k2_lattices(X1,X2,X0)) = k2_lattices(X1,k2_lattices(X1,X3,X2),X0)
% 15.33/2.51      | sK7 != X1 ),
% 15.33/2.51      inference(resolution_lifted,[status(thm)],[c_353,c_25]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_794,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 15.33/2.51      | ~ l3_lattices(sK7)
% 15.33/2.51      | v2_struct_0(sK7)
% 15.33/2.51      | k2_lattices(sK7,X2,k2_lattices(sK7,X0,X1)) = k2_lattices(sK7,k2_lattices(sK7,X2,X0),X1) ),
% 15.33/2.51      inference(unflattening,[status(thm)],[c_793]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_872,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 15.33/2.51      | k2_lattices(sK7,X2,k2_lattices(sK7,X0,X1)) = k2_lattices(sK7,k2_lattices(sK7,X2,X0),X1) ),
% 15.33/2.51      inference(global_propositional_subsumption,
% 15.33/2.51                [status(thm)],
% 15.33/2.51                [c_870,c_26,c_22,c_794]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_873,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 15.33/2.51      | k2_lattices(sK7,X0,k2_lattices(sK7,X1,X2)) = k2_lattices(sK7,k2_lattices(sK7,X0,X1),X2) ),
% 15.33/2.51      inference(renaming,[status(thm)],[c_872]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_1019,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0_50,u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(X1_50,u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(X2_50,u1_struct_0(sK7))
% 15.33/2.51      | k2_lattices(sK7,X0_50,k2_lattices(sK7,X1_50,X2_50)) = k2_lattices(sK7,k2_lattices(sK7,X0_50,X1_50),X2_50) ),
% 15.33/2.51      inference(subtyping,[status(esa)],[c_873]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_1177,plain,
% 15.33/2.51      ( k2_lattices(sK7,X0_50,k2_lattices(sK7,X1_50,X2_50)) = k2_lattices(sK7,k2_lattices(sK7,X0_50,X1_50),X2_50)
% 15.33/2.51      | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
% 15.33/2.51      | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
% 15.33/2.51      | m1_subset_1(X2_50,u1_struct_0(sK7)) != iProver_top ),
% 15.33/2.51      inference(predicate_to_equality,[status(thm)],[c_1019]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_1854,plain,
% 15.33/2.51      ( k2_lattices(sK7,k2_lattices(sK7,sK9,X0_50),X1_50) = k2_lattices(sK7,sK9,k2_lattices(sK7,X0_50,X1_50))
% 15.33/2.51      | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
% 15.33/2.51      | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top ),
% 15.33/2.51      inference(superposition,[status(thm)],[c_1172,c_1177]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_2772,plain,
% 15.33/2.51      ( k2_lattices(sK7,sK9,k2_lattices(sK7,sK10,X0_50)) = k2_lattices(sK7,k2_lattices(sK7,sK9,sK10),X0_50)
% 15.33/2.51      | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
% 15.33/2.51      inference(superposition,[status(thm)],[c_1171,c_1854]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_3741,plain,
% 15.33/2.51      ( k2_lattices(sK7,sK9,k2_lattices(sK7,sK10,sK10)) = k2_lattices(sK7,k2_lattices(sK7,sK9,sK10),sK10) ),
% 15.33/2.51      inference(superposition,[status(thm)],[c_1171,c_2772]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_13,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.33/2.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.33/2.51      | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
% 15.33/2.51      | v2_struct_0(X1)
% 15.33/2.51      | ~ l1_lattices(X1) ),
% 15.33/2.51      inference(cnf_transformation,[],[f58]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_331,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.33/2.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.33/2.51      | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
% 15.33/2.51      | ~ l3_lattices(X3)
% 15.33/2.51      | v2_struct_0(X1)
% 15.33/2.51      | X1 != X3 ),
% 15.33/2.51      inference(resolution_lifted,[status(thm)],[c_14,c_13]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_332,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.33/2.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.33/2.51      | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
% 15.33/2.51      | ~ l3_lattices(X1)
% 15.33/2.51      | v2_struct_0(X1) ),
% 15.33/2.51      inference(unflattening,[status(thm)],[c_331]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_889,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.33/2.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.33/2.51      | m1_subset_1(k2_lattices(X1,X2,X0),u1_struct_0(X1))
% 15.33/2.51      | ~ l3_lattices(X1)
% 15.33/2.51      | sK7 != X1 ),
% 15.33/2.51      inference(resolution_lifted,[status(thm)],[c_332,c_26]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_890,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 15.33/2.51      | m1_subset_1(k2_lattices(sK7,X0,X1),u1_struct_0(sK7))
% 15.33/2.51      | ~ l3_lattices(sK7) ),
% 15.33/2.51      inference(unflattening,[status(thm)],[c_889]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_894,plain,
% 15.33/2.51      ( m1_subset_1(k2_lattices(sK7,X0,X1),u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 15.33/2.51      inference(global_propositional_subsumption,
% 15.33/2.51                [status(thm)],
% 15.33/2.51                [c_890,c_22]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_895,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 15.33/2.51      | m1_subset_1(k2_lattices(sK7,X0,X1),u1_struct_0(sK7)) ),
% 15.33/2.51      inference(renaming,[status(thm)],[c_894]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_1018,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0_50,u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(X1_50,u1_struct_0(sK7))
% 15.33/2.51      | m1_subset_1(k2_lattices(sK7,X0_50,X1_50),u1_struct_0(sK7)) ),
% 15.33/2.51      inference(subtyping,[status(esa)],[c_895]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_1178,plain,
% 15.33/2.51      ( m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
% 15.33/2.51      | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
% 15.33/2.51      | m1_subset_1(k2_lattices(sK7,X0_50,X1_50),u1_struct_0(sK7)) = iProver_top ),
% 15.33/2.51      inference(predicate_to_equality,[status(thm)],[c_1018]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_3761,plain,
% 15.33/2.51      ( m1_subset_1(k2_lattices(sK7,sK9,k2_lattices(sK7,sK10,sK10)),u1_struct_0(sK7)) = iProver_top
% 15.33/2.51      | m1_subset_1(k2_lattices(sK7,sK9,sK10),u1_struct_0(sK7)) != iProver_top
% 15.33/2.51      | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top ),
% 15.33/2.51      inference(superposition,[status(thm)],[c_3741,c_1178]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_33,plain,
% 15.33/2.51      ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
% 15.33/2.51      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_34,plain,
% 15.33/2.51      ( m1_subset_1(sK10,u1_struct_0(sK7)) = iProver_top ),
% 15.33/2.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_1240,plain,
% 15.33/2.51      ( m1_subset_1(k2_lattices(sK7,sK9,sK10),u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(sK9,u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(sK10,u1_struct_0(sK7)) ),
% 15.33/2.51      inference(instantiation,[status(thm)],[c_1018]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_1241,plain,
% 15.33/2.51      ( m1_subset_1(k2_lattices(sK7,sK9,sK10),u1_struct_0(sK7)) = iProver_top
% 15.33/2.51      | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
% 15.33/2.51      | m1_subset_1(sK10,u1_struct_0(sK7)) != iProver_top ),
% 15.33/2.51      inference(predicate_to_equality,[status(thm)],[c_1240]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_51677,plain,
% 15.33/2.51      ( m1_subset_1(k2_lattices(sK7,sK9,k2_lattices(sK7,sK10,sK10)),u1_struct_0(sK7)) = iProver_top ),
% 15.33/2.51      inference(global_propositional_subsumption,
% 15.33/2.51                [status(thm)],
% 15.33/2.51                [c_3761,c_33,c_34,c_1241]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_12,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.33/2.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.33/2.51      | ~ v9_lattices(X1)
% 15.33/2.51      | ~ l3_lattices(X1)
% 15.33/2.51      | v2_struct_0(X1)
% 15.33/2.51      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2 ),
% 15.33/2.51      inference(cnf_transformation,[],[f54]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_910,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.33/2.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.33/2.51      | ~ v9_lattices(X1)
% 15.33/2.51      | ~ l3_lattices(X1)
% 15.33/2.51      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
% 15.33/2.51      | sK7 != X1 ),
% 15.33/2.51      inference(resolution_lifted,[status(thm)],[c_12,c_26]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_911,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 15.33/2.51      | ~ v9_lattices(sK7)
% 15.33/2.51      | ~ l3_lattices(sK7)
% 15.33/2.51      | k2_lattices(sK7,X0,k1_lattices(sK7,X0,X1)) = X0 ),
% 15.33/2.51      inference(unflattening,[status(thm)],[c_910]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_23,negated_conjecture,
% 15.33/2.51      ( v9_lattices(sK7) ),
% 15.33/2.51      inference(cnf_transformation,[],[f65]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_643,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.33/2.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.33/2.51      | ~ l3_lattices(X1)
% 15.33/2.51      | v2_struct_0(X1)
% 15.33/2.51      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
% 15.33/2.51      | sK7 != X1 ),
% 15.33/2.51      inference(resolution_lifted,[status(thm)],[c_12,c_23]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_644,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 15.33/2.51      | ~ l3_lattices(sK7)
% 15.33/2.51      | v2_struct_0(sK7)
% 15.33/2.51      | k2_lattices(sK7,X0,k1_lattices(sK7,X0,X1)) = X0 ),
% 15.33/2.51      inference(unflattening,[status(thm)],[c_643]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_648,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 15.33/2.51      | k2_lattices(sK7,X0,k1_lattices(sK7,X0,X1)) = X0 ),
% 15.33/2.51      inference(global_propositional_subsumption,
% 15.33/2.51                [status(thm)],
% 15.33/2.51                [c_644,c_26,c_22]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_913,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 15.33/2.51      | k2_lattices(sK7,X0,k1_lattices(sK7,X0,X1)) = X0 ),
% 15.33/2.51      inference(global_propositional_subsumption,
% 15.33/2.51                [status(thm)],
% 15.33/2.51                [c_911,c_26,c_22,c_644]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_1020,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0_50,u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(X1_50,u1_struct_0(sK7))
% 15.33/2.51      | k2_lattices(sK7,X0_50,k1_lattices(sK7,X0_50,X1_50)) = X0_50 ),
% 15.33/2.51      inference(subtyping,[status(esa)],[c_913]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_1176,plain,
% 15.33/2.51      ( k2_lattices(sK7,X0_50,k1_lattices(sK7,X0_50,X1_50)) = X0_50
% 15.33/2.51      | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
% 15.33/2.51      | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top ),
% 15.33/2.51      inference(predicate_to_equality,[status(thm)],[c_1020]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_2591,plain,
% 15.33/2.51      ( k2_lattices(sK7,k2_lattices(sK7,X0_50,X1_50),k1_lattices(sK7,k2_lattices(sK7,X0_50,X1_50),X2_50)) = k2_lattices(sK7,X0_50,X1_50)
% 15.33/2.51      | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
% 15.33/2.51      | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top
% 15.33/2.51      | m1_subset_1(X2_50,u1_struct_0(sK7)) != iProver_top ),
% 15.33/2.51      inference(superposition,[status(thm)],[c_1178,c_1176]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_8792,plain,
% 15.33/2.51      ( k2_lattices(sK7,k2_lattices(sK7,sK9,X0_50),k1_lattices(sK7,k2_lattices(sK7,sK9,X0_50),X1_50)) = k2_lattices(sK7,sK9,X0_50)
% 15.33/2.51      | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
% 15.33/2.51      | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top ),
% 15.33/2.51      inference(superposition,[status(thm)],[c_1172,c_2591]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_9851,plain,
% 15.33/2.51      ( k2_lattices(sK7,k2_lattices(sK7,sK9,sK10),k1_lattices(sK7,k2_lattices(sK7,sK9,sK10),X0_50)) = k2_lattices(sK7,sK9,sK10)
% 15.33/2.51      | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
% 15.33/2.51      inference(superposition,[status(thm)],[c_1171,c_8792]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_10016,plain,
% 15.33/2.51      ( k2_lattices(sK7,k2_lattices(sK7,sK9,sK10),k1_lattices(sK7,k2_lattices(sK7,sK9,sK10),sK10)) = k2_lattices(sK7,sK9,sK10) ),
% 15.33/2.51      inference(superposition,[status(thm)],[c_1171,c_9851]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_8,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.33/2.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.33/2.51      | ~ l3_lattices(X1)
% 15.33/2.51      | ~ v8_lattices(X1)
% 15.33/2.51      | v2_struct_0(X1)
% 15.33/2.51      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 ),
% 15.33/2.51      inference(cnf_transformation,[],[f50]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_927,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.33/2.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.33/2.51      | ~ l3_lattices(X1)
% 15.33/2.51      | ~ v8_lattices(X1)
% 15.33/2.51      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
% 15.33/2.51      | sK7 != X1 ),
% 15.33/2.51      inference(resolution_lifted,[status(thm)],[c_8,c_26]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_928,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 15.33/2.51      | ~ l3_lattices(sK7)
% 15.33/2.51      | ~ v8_lattices(sK7)
% 15.33/2.51      | k1_lattices(sK7,k2_lattices(sK7,X0,X1),X1) = X1 ),
% 15.33/2.51      inference(unflattening,[status(thm)],[c_927]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_24,negated_conjecture,
% 15.33/2.51      ( v8_lattices(sK7) ),
% 15.33/2.51      inference(cnf_transformation,[],[f64]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_529,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.33/2.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.33/2.51      | ~ l3_lattices(X1)
% 15.33/2.51      | v2_struct_0(X1)
% 15.33/2.51      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
% 15.33/2.51      | sK7 != X1 ),
% 15.33/2.51      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_530,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 15.33/2.51      | ~ l3_lattices(sK7)
% 15.33/2.51      | v2_struct_0(sK7)
% 15.33/2.51      | k1_lattices(sK7,k2_lattices(sK7,X0,X1),X1) = X1 ),
% 15.33/2.51      inference(unflattening,[status(thm)],[c_529]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_534,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 15.33/2.51      | k1_lattices(sK7,k2_lattices(sK7,X0,X1),X1) = X1 ),
% 15.33/2.51      inference(global_propositional_subsumption,
% 15.33/2.51                [status(thm)],
% 15.33/2.51                [c_530,c_26,c_22]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_930,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 15.33/2.51      | k1_lattices(sK7,k2_lattices(sK7,X0,X1),X1) = X1 ),
% 15.33/2.51      inference(global_propositional_subsumption,
% 15.33/2.51                [status(thm)],
% 15.33/2.51                [c_928,c_26,c_22,c_530]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_1021,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0_50,u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(X1_50,u1_struct_0(sK7))
% 15.33/2.51      | k1_lattices(sK7,k2_lattices(sK7,X0_50,X1_50),X1_50) = X1_50 ),
% 15.33/2.51      inference(subtyping,[status(esa)],[c_930]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_1175,plain,
% 15.33/2.51      ( k1_lattices(sK7,k2_lattices(sK7,X0_50,X1_50),X1_50) = X1_50
% 15.33/2.51      | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
% 15.33/2.51      | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top ),
% 15.33/2.51      inference(predicate_to_equality,[status(thm)],[c_1021]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_1319,plain,
% 15.33/2.51      ( k1_lattices(sK7,k2_lattices(sK7,sK9,X0_50),X0_50) = X0_50
% 15.33/2.51      | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
% 15.33/2.51      inference(superposition,[status(thm)],[c_1172,c_1175]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_1497,plain,
% 15.33/2.51      ( k1_lattices(sK7,k2_lattices(sK7,sK9,sK10),sK10) = sK10 ),
% 15.33/2.51      inference(superposition,[status(thm)],[c_1171,c_1319]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_10031,plain,
% 15.33/2.51      ( k2_lattices(sK7,sK9,k2_lattices(sK7,sK10,sK10)) = k2_lattices(sK7,sK9,sK10) ),
% 15.33/2.51      inference(light_normalisation,
% 15.33/2.51                [status(thm)],
% 15.33/2.51                [c_10016,c_1497,c_3741]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_51681,plain,
% 15.33/2.51      ( m1_subset_1(k2_lattices(sK7,sK9,sK10),u1_struct_0(sK7)) = iProver_top ),
% 15.33/2.51      inference(light_normalisation,[status(thm)],[c_51677,c_10031]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_21,negated_conjecture,
% 15.33/2.51      ( m1_subset_1(sK8,u1_struct_0(sK7)) ),
% 15.33/2.51      inference(cnf_transformation,[],[f67]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_1024,negated_conjecture,
% 15.33/2.51      ( m1_subset_1(sK8,u1_struct_0(sK7)) ),
% 15.33/2.51      inference(subtyping,[status(esa)],[c_21]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_1173,plain,
% 15.33/2.51      ( m1_subset_1(sK8,u1_struct_0(sK7)) = iProver_top ),
% 15.33/2.51      inference(predicate_to_equality,[status(thm)],[c_1024]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_8793,plain,
% 15.33/2.51      ( k2_lattices(sK7,k2_lattices(sK7,sK8,X0_50),k1_lattices(sK7,k2_lattices(sK7,sK8,X0_50),X1_50)) = k2_lattices(sK7,sK8,X0_50)
% 15.33/2.51      | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
% 15.33/2.51      | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top ),
% 15.33/2.51      inference(superposition,[status(thm)],[c_1173,c_2591]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_16046,plain,
% 15.33/2.51      ( k2_lattices(sK7,k2_lattices(sK7,sK8,sK10),k1_lattices(sK7,k2_lattices(sK7,sK8,sK10),X0_50)) = k2_lattices(sK7,sK8,sK10)
% 15.33/2.51      | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
% 15.33/2.51      inference(superposition,[status(thm)],[c_1171,c_8793]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_51731,plain,
% 15.33/2.51      ( k2_lattices(sK7,k2_lattices(sK7,sK8,sK10),k1_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10))) = k2_lattices(sK7,sK8,sK10) ),
% 15.33/2.51      inference(superposition,[status(thm)],[c_51681,c_16046]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_1320,plain,
% 15.33/2.51      ( k1_lattices(sK7,k2_lattices(sK7,sK8,X0_50),X0_50) = X0_50
% 15.33/2.51      | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
% 15.33/2.51      inference(superposition,[status(thm)],[c_1173,c_1175]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_2592,plain,
% 15.33/2.51      ( k1_lattices(sK7,k2_lattices(sK7,sK8,k2_lattices(sK7,X0_50,X1_50)),k2_lattices(sK7,X0_50,X1_50)) = k2_lattices(sK7,X0_50,X1_50)
% 15.33/2.51      | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
% 15.33/2.51      | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top ),
% 15.33/2.51      inference(superposition,[status(thm)],[c_1178,c_1320]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_10041,plain,
% 15.33/2.51      ( k1_lattices(sK7,k2_lattices(sK7,sK8,k2_lattices(sK7,sK9,X0_50)),k2_lattices(sK7,sK9,X0_50)) = k2_lattices(sK7,sK9,X0_50)
% 15.33/2.51      | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
% 15.33/2.51      inference(superposition,[status(thm)],[c_1172,c_2592]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_11181,plain,
% 15.33/2.51      ( k1_lattices(sK7,k2_lattices(sK7,sK8,k2_lattices(sK7,sK9,sK10)),k2_lattices(sK7,sK9,sK10)) = k2_lattices(sK7,sK9,sK10) ),
% 15.33/2.51      inference(superposition,[status(thm)],[c_1171,c_10041]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_1855,plain,
% 15.33/2.51      ( k2_lattices(sK7,k2_lattices(sK7,sK8,X0_50),X1_50) = k2_lattices(sK7,sK8,k2_lattices(sK7,X0_50,X1_50))
% 15.33/2.51      | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top
% 15.33/2.51      | m1_subset_1(X1_50,u1_struct_0(sK7)) != iProver_top ),
% 15.33/2.51      inference(superposition,[status(thm)],[c_1173,c_1177]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_3545,plain,
% 15.33/2.51      ( k2_lattices(sK7,sK8,k2_lattices(sK7,sK9,X0_50)) = k2_lattices(sK7,k2_lattices(sK7,sK8,sK9),X0_50)
% 15.33/2.51      | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
% 15.33/2.51      inference(superposition,[status(thm)],[c_1172,c_1855]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_16,plain,
% 15.33/2.51      ( ~ r1_lattices(X0,X1,X2)
% 15.33/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.33/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.33/2.51      | ~ v9_lattices(X0)
% 15.33/2.51      | ~ l3_lattices(X0)
% 15.33/2.51      | ~ v8_lattices(X0)
% 15.33/2.51      | v2_struct_0(X0)
% 15.33/2.51      | k2_lattices(X0,X1,X2) = X1 ),
% 15.33/2.51      inference(cnf_transformation,[],[f60]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_18,negated_conjecture,
% 15.33/2.51      ( r1_lattices(sK7,sK8,sK9) ),
% 15.33/2.51      inference(cnf_transformation,[],[f70]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_431,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.33/2.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.33/2.51      | ~ v9_lattices(X1)
% 15.33/2.51      | ~ l3_lattices(X1)
% 15.33/2.51      | ~ v8_lattices(X1)
% 15.33/2.51      | v2_struct_0(X1)
% 15.33/2.51      | k2_lattices(X1,X2,X0) = X2
% 15.33/2.51      | sK9 != X0
% 15.33/2.51      | sK8 != X2
% 15.33/2.51      | sK7 != X1 ),
% 15.33/2.51      inference(resolution_lifted,[status(thm)],[c_16,c_18]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_432,plain,
% 15.33/2.51      ( ~ m1_subset_1(sK9,u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(sK8,u1_struct_0(sK7))
% 15.33/2.51      | ~ v9_lattices(sK7)
% 15.33/2.51      | ~ l3_lattices(sK7)
% 15.33/2.51      | ~ v8_lattices(sK7)
% 15.33/2.51      | v2_struct_0(sK7)
% 15.33/2.51      | k2_lattices(sK7,sK8,sK9) = sK8 ),
% 15.33/2.51      inference(unflattening,[status(thm)],[c_431]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_434,plain,
% 15.33/2.51      ( k2_lattices(sK7,sK8,sK9) = sK8 ),
% 15.33/2.51      inference(global_propositional_subsumption,
% 15.33/2.51                [status(thm)],
% 15.33/2.51                [c_432,c_26,c_24,c_23,c_22,c_21,c_20]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_1022,plain,
% 15.33/2.51      ( k2_lattices(sK7,sK8,sK9) = sK8 ),
% 15.33/2.51      inference(subtyping,[status(esa)],[c_434]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_3562,plain,
% 15.33/2.51      ( k2_lattices(sK7,sK8,k2_lattices(sK7,sK9,X0_50)) = k2_lattices(sK7,sK8,X0_50)
% 15.33/2.51      | m1_subset_1(X0_50,u1_struct_0(sK7)) != iProver_top ),
% 15.33/2.51      inference(light_normalisation,[status(thm)],[c_3545,c_1022]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_4016,plain,
% 15.33/2.51      ( k2_lattices(sK7,sK8,k2_lattices(sK7,sK9,sK10)) = k2_lattices(sK7,sK8,sK10) ),
% 15.33/2.51      inference(superposition,[status(thm)],[c_1171,c_3562]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_11198,plain,
% 15.33/2.51      ( k1_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10)) = k2_lattices(sK7,sK9,sK10) ),
% 15.33/2.51      inference(light_normalisation,[status(thm)],[c_11181,c_4016]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_51952,plain,
% 15.33/2.51      ( k2_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10)) = k2_lattices(sK7,sK8,sK10) ),
% 15.33/2.51      inference(light_normalisation,[status(thm)],[c_51731,c_11198]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_1288,plain,
% 15.33/2.51      ( m1_subset_1(k2_lattices(sK7,sK8,sK10),u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(sK10,u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
% 15.33/2.51      inference(instantiation,[status(thm)],[c_1018]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_15,plain,
% 15.33/2.51      ( r1_lattices(X0,X1,X2)
% 15.33/2.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.33/2.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.33/2.51      | ~ v9_lattices(X0)
% 15.33/2.51      | ~ l3_lattices(X0)
% 15.33/2.51      | ~ v8_lattices(X0)
% 15.33/2.51      | v2_struct_0(X0)
% 15.33/2.51      | k2_lattices(X0,X1,X2) != X1 ),
% 15.33/2.51      inference(cnf_transformation,[],[f61]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_17,negated_conjecture,
% 15.33/2.51      ( ~ r1_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10)) ),
% 15.33/2.51      inference(cnf_transformation,[],[f71]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_414,plain,
% 15.33/2.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.33/2.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.33/2.51      | ~ v9_lattices(X1)
% 15.33/2.51      | ~ l3_lattices(X1)
% 15.33/2.51      | ~ v8_lattices(X1)
% 15.33/2.51      | v2_struct_0(X1)
% 15.33/2.51      | k2_lattices(X1,X2,X0) != X2
% 15.33/2.51      | k2_lattices(sK7,sK9,sK10) != X0
% 15.33/2.51      | k2_lattices(sK7,sK8,sK10) != X2
% 15.33/2.51      | sK7 != X1 ),
% 15.33/2.51      inference(resolution_lifted,[status(thm)],[c_15,c_17]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_415,plain,
% 15.33/2.51      ( ~ m1_subset_1(k2_lattices(sK7,sK9,sK10),u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(k2_lattices(sK7,sK8,sK10),u1_struct_0(sK7))
% 15.33/2.51      | ~ v9_lattices(sK7)
% 15.33/2.51      | ~ l3_lattices(sK7)
% 15.33/2.51      | ~ v8_lattices(sK7)
% 15.33/2.51      | v2_struct_0(sK7)
% 15.33/2.51      | k2_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10)) != k2_lattices(sK7,sK8,sK10) ),
% 15.33/2.51      inference(unflattening,[status(thm)],[c_414]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_417,plain,
% 15.33/2.51      ( ~ m1_subset_1(k2_lattices(sK7,sK9,sK10),u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(k2_lattices(sK7,sK8,sK10),u1_struct_0(sK7))
% 15.33/2.51      | k2_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10)) != k2_lattices(sK7,sK8,sK10) ),
% 15.33/2.51      inference(global_propositional_subsumption,
% 15.33/2.51                [status(thm)],
% 15.33/2.51                [c_415,c_26,c_24,c_23,c_22]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(c_1023,plain,
% 15.33/2.51      ( ~ m1_subset_1(k2_lattices(sK7,sK9,sK10),u1_struct_0(sK7))
% 15.33/2.51      | ~ m1_subset_1(k2_lattices(sK7,sK8,sK10),u1_struct_0(sK7))
% 15.33/2.51      | k2_lattices(sK7,k2_lattices(sK7,sK8,sK10),k2_lattices(sK7,sK9,sK10)) != k2_lattices(sK7,sK8,sK10) ),
% 15.33/2.51      inference(subtyping,[status(esa)],[c_417]) ).
% 15.33/2.51  
% 15.33/2.51  cnf(contradiction,plain,
% 15.33/2.51      ( $false ),
% 15.33/2.51      inference(minisat,
% 15.33/2.51                [status(thm)],
% 15.33/2.51                [c_51952,c_1288,c_1240,c_1023,c_19,c_20,c_21]) ).
% 15.33/2.51  
% 15.33/2.51  
% 15.33/2.51  % SZS output end CNFRefutation for theBenchmark.p
% 15.33/2.51  
% 15.33/2.51  ------                               Statistics
% 15.33/2.51  
% 15.33/2.51  ------ General
% 15.33/2.51  
% 15.33/2.51  abstr_ref_over_cycles:                  0
% 15.33/2.51  abstr_ref_under_cycles:                 0
% 15.33/2.51  gc_basic_clause_elim:                   0
% 15.33/2.51  forced_gc_time:                         0
% 15.33/2.51  parsing_time:                           0.007
% 15.33/2.51  unif_index_cands_time:                  0.
% 15.33/2.51  unif_index_add_time:                    0.
% 15.33/2.51  orderings_time:                         0.
% 15.33/2.51  out_proof_time:                         0.018
% 15.33/2.51  total_time:                             1.763
% 15.33/2.51  num_of_symbols:                         53
% 15.33/2.51  num_of_terms:                           59229
% 15.33/2.51  
% 15.33/2.51  ------ Preprocessing
% 15.33/2.51  
% 15.33/2.51  num_of_splits:                          0
% 15.33/2.51  num_of_split_atoms:                     0
% 15.33/2.51  num_of_reused_defs:                     0
% 15.33/2.51  num_eq_ax_congr_red:                    15
% 15.33/2.51  num_of_sem_filtered_clauses:            1
% 15.33/2.51  num_of_subtypes:                        3
% 15.33/2.51  monotx_restored_types:                  0
% 15.33/2.51  sat_num_of_epr_types:                   0
% 15.33/2.51  sat_num_of_non_cyclic_types:            0
% 15.33/2.51  sat_guarded_non_collapsed_types:        1
% 15.33/2.51  num_pure_diseq_elim:                    0
% 15.33/2.51  simp_replaced_by:                       0
% 15.33/2.51  res_preprocessed:                       68
% 15.33/2.51  prep_upred:                             0
% 15.33/2.51  prep_unflattend:                        35
% 15.33/2.51  smt_new_axioms:                         0
% 15.33/2.51  pred_elim_cands:                        1
% 15.33/2.51  pred_elim:                              7
% 15.33/2.51  pred_elim_cl:                           17
% 15.33/2.51  pred_elim_cycles:                       12
% 15.33/2.51  merged_defs:                            0
% 15.33/2.51  merged_defs_ncl:                        0
% 15.33/2.51  bin_hyper_res:                          0
% 15.33/2.51  prep_cycles:                            4
% 15.33/2.51  pred_elim_time:                         0.027
% 15.33/2.51  splitting_time:                         0.
% 15.33/2.51  sem_filter_time:                        0.
% 15.33/2.51  monotx_time:                            0.
% 15.33/2.51  subtype_inf_time:                       0.
% 15.33/2.51  
% 15.33/2.51  ------ Problem properties
% 15.33/2.51  
% 15.33/2.51  clauses:                                10
% 15.33/2.51  conjectures:                            3
% 15.33/2.51  epr:                                    0
% 15.33/2.51  horn:                                   10
% 15.33/2.51  ground:                                 6
% 15.33/2.51  unary:                                  4
% 15.33/2.51  binary:                                 1
% 15.33/2.51  lits:                                   22
% 15.33/2.51  lits_eq:                                7
% 15.33/2.51  fd_pure:                                0
% 15.33/2.51  fd_pseudo:                              0
% 15.33/2.51  fd_cond:                                0
% 15.33/2.51  fd_pseudo_cond:                         0
% 15.33/2.51  ac_symbols:                             0
% 15.33/2.51  
% 15.33/2.51  ------ Propositional Solver
% 15.33/2.51  
% 15.33/2.51  prop_solver_calls:                      34
% 15.33/2.51  prop_fast_solver_calls:                 1128
% 15.33/2.51  smt_solver_calls:                       0
% 15.33/2.51  smt_fast_solver_calls:                  0
% 15.33/2.51  prop_num_of_clauses:                    15944
% 15.33/2.51  prop_preprocess_simplified:             27814
% 15.33/2.51  prop_fo_subsumed:                       41
% 15.33/2.51  prop_solver_time:                       0.
% 15.33/2.51  smt_solver_time:                        0.
% 15.33/2.51  smt_fast_solver_time:                   0.
% 15.33/2.51  prop_fast_solver_time:                  0.
% 15.33/2.51  prop_unsat_core_time:                   0.002
% 15.33/2.51  
% 15.33/2.51  ------ QBF
% 15.33/2.51  
% 15.33/2.51  qbf_q_res:                              0
% 15.33/2.51  qbf_num_tautologies:                    0
% 15.33/2.51  qbf_prep_cycles:                        0
% 15.33/2.51  
% 15.33/2.51  ------ BMC1
% 15.33/2.51  
% 15.33/2.51  bmc1_current_bound:                     -1
% 15.33/2.51  bmc1_last_solved_bound:                 -1
% 15.33/2.51  bmc1_unsat_core_size:                   -1
% 15.33/2.51  bmc1_unsat_core_parents_size:           -1
% 15.33/2.51  bmc1_merge_next_fun:                    0
% 15.33/2.51  bmc1_unsat_core_clauses_time:           0.
% 15.33/2.51  
% 15.33/2.51  ------ Instantiation
% 15.33/2.51  
% 15.33/2.51  inst_num_of_clauses:                    6372
% 15.33/2.51  inst_num_in_passive:                    3012
% 15.33/2.51  inst_num_in_active:                     1645
% 15.33/2.51  inst_num_in_unprocessed:                1715
% 15.33/2.51  inst_num_of_loops:                      1820
% 15.33/2.51  inst_num_of_learning_restarts:          0
% 15.33/2.51  inst_num_moves_active_passive:          169
% 15.33/2.51  inst_lit_activity:                      0
% 15.33/2.51  inst_lit_activity_moves:                1
% 15.33/2.51  inst_num_tautologies:                   0
% 15.33/2.51  inst_num_prop_implied:                  0
% 15.33/2.51  inst_num_existing_simplified:           0
% 15.33/2.51  inst_num_eq_res_simplified:             0
% 15.33/2.51  inst_num_child_elim:                    0
% 15.33/2.51  inst_num_of_dismatching_blockings:      12624
% 15.33/2.51  inst_num_of_non_proper_insts:           8409
% 15.33/2.51  inst_num_of_duplicates:                 0
% 15.33/2.51  inst_inst_num_from_inst_to_res:         0
% 15.33/2.51  inst_dismatching_checking_time:         0.
% 15.33/2.51  
% 15.33/2.51  ------ Resolution
% 15.33/2.51  
% 15.33/2.51  res_num_of_clauses:                     0
% 15.33/2.51  res_num_in_passive:                     0
% 15.33/2.51  res_num_in_active:                      0
% 15.33/2.51  res_num_of_loops:                       72
% 15.33/2.51  res_forward_subset_subsumed:            340
% 15.33/2.51  res_backward_subset_subsumed:           2
% 15.33/2.51  res_forward_subsumed:                   0
% 15.33/2.51  res_backward_subsumed:                  0
% 15.33/2.51  res_forward_subsumption_resolution:     0
% 15.33/2.51  res_backward_subsumption_resolution:    0
% 15.33/2.51  res_clause_to_clause_subsumption:       3218
% 15.33/2.51  res_orphan_elimination:                 0
% 15.33/2.51  res_tautology_del:                      869
% 15.33/2.51  res_num_eq_res_simplified:              1
% 15.33/2.51  res_num_sel_changes:                    0
% 15.33/2.51  res_moves_from_active_to_pass:          0
% 15.33/2.51  
% 15.33/2.51  ------ Superposition
% 15.33/2.51  
% 15.33/2.51  sup_time_total:                         0.
% 15.33/2.51  sup_time_generating:                    0.
% 15.33/2.51  sup_time_sim_full:                      0.
% 15.33/2.51  sup_time_sim_immed:                     0.
% 15.33/2.51  
% 15.33/2.51  sup_num_of_clauses:                     1406
% 15.33/2.51  sup_num_in_active:                      333
% 15.33/2.51  sup_num_in_passive:                     1073
% 15.33/2.51  sup_num_of_loops:                       363
% 15.33/2.51  sup_fw_superposition:                   609
% 15.33/2.51  sup_bw_superposition:                   1032
% 15.33/2.51  sup_immediate_simplified:               468
% 15.33/2.51  sup_given_eliminated:                   0
% 15.33/2.51  comparisons_done:                       0
% 15.33/2.51  comparisons_avoided:                    0
% 15.33/2.51  
% 15.33/2.51  ------ Simplifications
% 15.33/2.51  
% 15.33/2.51  
% 15.33/2.51  sim_fw_subset_subsumed:                 75
% 15.33/2.51  sim_bw_subset_subsumed:                 2
% 15.33/2.51  sim_fw_subsumed:                        3
% 15.33/2.51  sim_bw_subsumed:                        0
% 15.33/2.51  sim_fw_subsumption_res:                 0
% 15.33/2.51  sim_bw_subsumption_res:                 0
% 15.33/2.51  sim_tautology_del:                      10
% 15.33/2.51  sim_eq_tautology_del:                   29
% 15.33/2.51  sim_eq_res_simp:                        0
% 15.33/2.51  sim_fw_demodulated:                     0
% 15.33/2.51  sim_bw_demodulated:                     33
% 15.33/2.51  sim_light_normalised:                   399
% 15.33/2.51  sim_joinable_taut:                      0
% 15.33/2.51  sim_joinable_simp:                      0
% 15.33/2.51  sim_ac_normalised:                      0
% 15.33/2.51  sim_smt_subsumption:                    0
% 15.33/2.51  
%------------------------------------------------------------------------------
