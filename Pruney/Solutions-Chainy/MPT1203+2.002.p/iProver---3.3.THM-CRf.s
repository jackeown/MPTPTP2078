%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:14 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 3.76s
% Verified   : 
% Statistics : Number of formulae       :  189 (2489 expanded)
%              Number of clauses        :  122 ( 550 expanded)
%              Number of leaves         :   18 ( 854 expanded)
%              Depth                    :   24
%              Number of atoms          :  736 (19490 expanded)
%              Number of equality atoms :  220 (6487 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v11_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                      & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) )
                   => X2 = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v11_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                        & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) )
                     => X2 = X3 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                  & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v11_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                  & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v11_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( X2 != X3
          & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
          & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sK8 != X2
        & k3_lattices(X0,X1,sK8) = k3_lattices(X0,X1,X2)
        & k4_lattices(X0,X1,sK8) = k4_lattices(X0,X1,X2)
        & m1_subset_1(sK8,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
              & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( sK7 != X3
            & k3_lattices(X0,X1,sK7) = k3_lattices(X0,X1,X3)
            & k4_lattices(X0,X1,sK7) = k4_lattices(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK7,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                  & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( X2 != X3
                & k3_lattices(X0,sK6,X2) = k3_lattices(X0,sK6,X3)
                & k4_lattices(X0,sK6,X2) = k4_lattices(X0,sK6,X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( X2 != X3
                    & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                    & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v11_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & k3_lattices(sK5,X1,X2) = k3_lattices(sK5,X1,X3)
                  & k4_lattices(sK5,X1,X2) = k4_lattices(sK5,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(sK5)) )
              & m1_subset_1(X2,u1_struct_0(sK5)) )
          & m1_subset_1(X1,u1_struct_0(sK5)) )
      & l3_lattices(sK5)
      & v11_lattices(sK5)
      & v10_lattices(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( sK7 != sK8
    & k3_lattices(sK5,sK6,sK7) = k3_lattices(sK5,sK6,sK8)
    & k4_lattices(sK5,sK6,sK7) = k4_lattices(sK5,sK6,sK8)
    & m1_subset_1(sK8,u1_struct_0(sK5))
    & m1_subset_1(sK7,u1_struct_0(sK5))
    & m1_subset_1(sK6,u1_struct_0(sK5))
    & l3_lattices(sK5)
    & v11_lattices(sK5)
    & v10_lattices(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f30,f45,f44,f43,f42])).

fof(f70,plain,(
    m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v11_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ! [X3] :
                      ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6))
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f31])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,sK2(X0))) != k2_lattices(X0,X1,k1_lattices(X0,X2,sK2(X0)))
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( k1_lattices(X0,k2_lattices(X0,X1,sK1(X0)),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,sK1(X0),X3))
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k1_lattices(X0,k2_lattices(X0,sK0(X0),X2),k2_lattices(X0,sK0(X0),X3)) != k2_lattices(X0,sK0(X0),k1_lattices(X0,X2,X3))
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ( k1_lattices(X0,k2_lattices(X0,sK0(X0),sK1(X0)),k2_lattices(X0,sK0(X0),sK2(X0))) != k2_lattices(X0,sK0(X0),k1_lattices(X0,sK1(X0),sK2(X0)))
            & m1_subset_1(sK2(X0),u1_struct_0(X0))
            & m1_subset_1(sK1(X0),u1_struct_0(X0))
            & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6))
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f35,f34,f33])).

fof(f53,plain,(
    ! [X6,X4,X0,X5] :
      ( k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v11_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    v11_lattices(sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f69,plain,(
    l3_lattices(sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f13,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
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
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f14])).

fof(f49,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f67,plain,(
    v10_lattices(sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f63,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
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

fof(f22,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

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
    inference(flattening,[],[f22])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,k1_lattices(X0,X1,sK4(X0))) != X1
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f38,f40,f39])).

fof(f58,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f50,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f74,plain,(
    k3_lattices(sK5,sK6,sK7) = k3_lattices(sK5,sK6,sK8) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f73,plain,(
    k4_lattices(sK5,sK6,sK7) = k4_lattices(sK5,sK6,sK8) ),
    inference(cnf_transformation,[],[f46])).

fof(f75,plain,(
    sK7 != sK8 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_662,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_836,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_662])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_664,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_834,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_663,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_835,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_663])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_560,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X1)
    | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_28])).

cnf(c_561,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ v11_lattices(sK5)
    | ~ l3_lattices(sK5)
    | k1_lattices(sK5,k2_lattices(sK5,X2,X0),k2_lattices(sK5,X2,X1)) = k2_lattices(sK5,X2,k1_lattices(sK5,X0,X1)) ),
    inference(unflattening,[status(thm)],[c_560])).

cnf(c_26,negated_conjecture,
    ( v11_lattices(sK5) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_25,negated_conjecture,
    ( l3_lattices(sK5) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_565,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | k1_lattices(sK5,k2_lattices(sK5,X2,X0),k2_lattices(sK5,X2,X1)) = k2_lattices(sK5,X2,k1_lattices(sK5,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_561,c_26,c_25])).

cnf(c_566,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | k1_lattices(sK5,k2_lattices(sK5,X0,X1),k2_lattices(sK5,X0,X2)) = k2_lattices(sK5,X0,k1_lattices(sK5,X1,X2)) ),
    inference(renaming,[status(thm)],[c_565])).

cnf(c_656,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK5))
    | ~ m1_subset_1(X2_52,u1_struct_0(sK5))
    | k1_lattices(sK5,k2_lattices(sK5,X0_52,X1_52),k2_lattices(sK5,X0_52,X2_52)) = k2_lattices(sK5,X0_52,k1_lattices(sK5,X1_52,X2_52)) ),
    inference(subtyping,[status(esa)],[c_566])).

cnf(c_842,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,X0_52,X1_52),k2_lattices(sK5,X0_52,X2_52)) = k2_lattices(sK5,X0_52,k1_lattices(sK5,X1_52,X2_52))
    | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X2_52,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_656])).

cnf(c_3911,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK7,X0_52),k2_lattices(sK5,sK7,X1_52)) = k2_lattices(sK5,sK7,k1_lattices(sK5,X0_52,X1_52))
    | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_835,c_842])).

cnf(c_4633,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK7,sK8),k2_lattices(sK5,sK7,X0_52)) = k2_lattices(sK5,sK7,k1_lattices(sK5,sK8,X0_52))
    | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_834,c_3911])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_27,negated_conjecture,
    ( v10_lattices(sK5) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_286,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_27])).

cnf(c_287,plain,
    ( v6_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_78,plain,
    ( v6_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_289,plain,
    ( v6_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_287,c_28,c_27,c_25,c_78])).

cnf(c_314,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_289])).

cnf(c_315,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l1_lattices(sK5)
    | v2_struct_0(sK5)
    | k2_lattices(sK5,X0,X1) = k4_lattices(sK5,X0,X1) ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_16,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_43,plain,
    ( l1_lattices(sK5)
    | ~ l3_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_319,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k2_lattices(sK5,X0,X1) = k4_lattices(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_315,c_28,c_25,c_43])).

cnf(c_661,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK5))
    | k2_lattices(sK5,X0_52,X1_52) = k4_lattices(sK5,X0_52,X1_52) ),
    inference(subtyping,[status(esa)],[c_319])).

cnf(c_837,plain,
    ( k2_lattices(sK5,X0_52,X1_52) = k4_lattices(sK5,X0_52,X1_52)
    | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_661])).

cnf(c_1117,plain,
    ( k2_lattices(sK5,sK7,X0_52) = k4_lattices(sK5,sK7,X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_835,c_837])).

cnf(c_1741,plain,
    ( k2_lattices(sK5,sK7,sK8) = k4_lattices(sK5,sK7,sK8) ),
    inference(superposition,[status(thm)],[c_834,c_1117])).

cnf(c_4648,plain,
    ( k1_lattices(sK5,k4_lattices(sK5,sK7,sK8),k2_lattices(sK5,sK7,X0_52)) = k2_lattices(sK5,sK7,k1_lattices(sK5,sK8,X0_52))
    | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4633,c_1741])).

cnf(c_8018,plain,
    ( k1_lattices(sK5,k4_lattices(sK5,sK7,sK8),k2_lattices(sK5,sK7,sK6)) = k2_lattices(sK5,sK7,k1_lattices(sK5,sK8,sK6)) ),
    inference(superposition,[status(thm)],[c_836,c_4648])).

cnf(c_1743,plain,
    ( k2_lattices(sK5,sK7,sK6) = k4_lattices(sK5,sK7,sK6) ),
    inference(superposition,[status(thm)],[c_836,c_1117])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_275,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_27])).

cnf(c_276,plain,
    ( v4_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_75,plain,
    ( v4_lattices(sK5)
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_278,plain,
    ( v4_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_276,c_28,c_27,c_25,c_75])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_278])).

cnf(c_365,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l2_lattices(sK5)
    | v2_struct_0(sK5)
    | k1_lattices(sK5,X0,X1) = k3_lattices(sK5,X0,X1) ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_15,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_46,plain,
    ( l2_lattices(sK5)
    | ~ l3_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_369,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k1_lattices(sK5,X0,X1) = k3_lattices(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_365,c_28,c_25,c_46])).

cnf(c_659,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK5))
    | k1_lattices(sK5,X0_52,X1_52) = k3_lattices(sK5,X0_52,X1_52) ),
    inference(subtyping,[status(esa)],[c_369])).

cnf(c_839,plain,
    ( k1_lattices(sK5,X0_52,X1_52) = k3_lattices(sK5,X0_52,X1_52)
    | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_659])).

cnf(c_2305,plain,
    ( k1_lattices(sK5,sK7,X0_52) = k3_lattices(sK5,sK7,X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_835,c_839])).

cnf(c_3122,plain,
    ( k1_lattices(sK5,sK7,sK6) = k3_lattices(sK5,sK7,sK6) ),
    inference(superposition,[status(thm)],[c_836,c_2305])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_542,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v9_lattices(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_28])).

cnf(c_543,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | ~ v9_lattices(sK5)
    | k2_lattices(sK5,X0,k1_lattices(sK5,X0,X1)) = X0 ),
    inference(unflattening,[status(thm)],[c_542])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_297,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v9_lattices(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_27])).

cnf(c_298,plain,
    ( ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | v9_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_297])).

cnf(c_81,plain,
    ( ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ v10_lattices(sK5)
    | v9_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_300,plain,
    ( v9_lattices(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_298,c_28,c_27,c_25,c_81])).

cnf(c_486,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_300])).

cnf(c_487,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l3_lattices(sK5)
    | v2_struct_0(sK5)
    | k2_lattices(sK5,X0,k1_lattices(sK5,X0,X1)) = X0 ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_546,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k2_lattices(sK5,X0,k1_lattices(sK5,X0,X1)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_543,c_28,c_25,c_487])).

cnf(c_657,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK5))
    | k2_lattices(sK5,X0_52,k1_lattices(sK5,X0_52,X1_52)) = X0_52 ),
    inference(subtyping,[status(esa)],[c_546])).

cnf(c_841,plain,
    ( k2_lattices(sK5,X0_52,k1_lattices(sK5,X0_52,X1_52)) = X0_52
    | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_657])).

cnf(c_1023,plain,
    ( k2_lattices(sK5,sK7,k1_lattices(sK5,sK7,X0_52)) = sK7
    | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_835,c_841])).

cnf(c_1295,plain,
    ( k2_lattices(sK5,sK7,k1_lattices(sK5,sK7,sK6)) = sK7 ),
    inference(superposition,[status(thm)],[c_836,c_1023])).

cnf(c_3349,plain,
    ( k2_lattices(sK5,sK7,k3_lattices(sK5,sK7,sK6)) = sK7 ),
    inference(demodulation,[status(thm)],[c_3122,c_1295])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_385,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_278])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l2_lattices(sK5)
    | v2_struct_0(sK5)
    | k3_lattices(sK5,X0,X1) = k3_lattices(sK5,X1,X0) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k3_lattices(sK5,X0,X1) = k3_lattices(sK5,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_386,c_28,c_25,c_46])).

cnf(c_658,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK5))
    | k3_lattices(sK5,X0_52,X1_52) = k3_lattices(sK5,X1_52,X0_52) ),
    inference(subtyping,[status(esa)],[c_390])).

cnf(c_840,plain,
    ( k3_lattices(sK5,X0_52,X1_52) = k3_lattices(sK5,X1_52,X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_658])).

cnf(c_2960,plain,
    ( k3_lattices(sK5,X0_52,sK7) = k3_lattices(sK5,sK7,X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_835,c_840])).

cnf(c_4248,plain,
    ( k3_lattices(sK5,sK7,sK6) = k3_lattices(sK5,sK6,sK7) ),
    inference(superposition,[status(thm)],[c_836,c_2960])).

cnf(c_2959,plain,
    ( k3_lattices(sK5,X0_52,sK8) = k3_lattices(sK5,sK8,X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_834,c_840])).

cnf(c_3704,plain,
    ( k3_lattices(sK5,sK8,sK6) = k3_lattices(sK5,sK6,sK8) ),
    inference(superposition,[status(thm)],[c_836,c_2959])).

cnf(c_20,negated_conjecture,
    ( k3_lattices(sK5,sK6,sK7) = k3_lattices(sK5,sK6,sK8) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_666,negated_conjecture,
    ( k3_lattices(sK5,sK6,sK7) = k3_lattices(sK5,sK6,sK8) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_3939,plain,
    ( k3_lattices(sK5,sK8,sK6) = k3_lattices(sK5,sK6,sK7) ),
    inference(demodulation,[status(thm)],[c_3704,c_666])).

cnf(c_4252,plain,
    ( k3_lattices(sK5,sK7,sK6) = k3_lattices(sK5,sK8,sK6) ),
    inference(demodulation,[status(thm)],[c_4248,c_3939])).

cnf(c_2304,plain,
    ( k1_lattices(sK5,sK8,X0_52) = k3_lattices(sK5,sK8,X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_834,c_839])).

cnf(c_2836,plain,
    ( k1_lattices(sK5,sK8,sK6) = k3_lattices(sK5,sK8,sK6) ),
    inference(superposition,[status(thm)],[c_836,c_2304])).

cnf(c_4328,plain,
    ( k1_lattices(sK5,sK8,sK6) = k3_lattices(sK5,sK7,sK6) ),
    inference(demodulation,[status(thm)],[c_4252,c_2836])).

cnf(c_3910,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK8,X0_52),k2_lattices(sK5,sK8,X1_52)) = k2_lattices(sK5,sK8,k1_lattices(sK5,X0_52,X1_52))
    | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_834,c_842])).

cnf(c_4494,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK8,sK7),k2_lattices(sK5,sK8,X0_52)) = k2_lattices(sK5,sK8,k1_lattices(sK5,sK7,X0_52))
    | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_835,c_3910])).

cnf(c_4521,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK8,sK7),k2_lattices(sK5,sK8,sK6)) = k2_lattices(sK5,sK8,k1_lattices(sK5,sK7,sK6)) ),
    inference(superposition,[status(thm)],[c_836,c_4494])).

cnf(c_4523,plain,
    ( k1_lattices(sK5,k2_lattices(sK5,sK8,sK7),k2_lattices(sK5,sK8,sK6)) = k2_lattices(sK5,sK8,k3_lattices(sK5,sK7,sK6)) ),
    inference(light_normalisation,[status(thm)],[c_4521,c_3122])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_335,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_289])).

cnf(c_336,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ l1_lattices(sK5)
    | v2_struct_0(sK5)
    | k4_lattices(sK5,X0,X1) = k4_lattices(sK5,X1,X0) ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_340,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k4_lattices(sK5,X0,X1) = k4_lattices(sK5,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_336,c_28,c_25,c_43])).

cnf(c_660,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK5))
    | k4_lattices(sK5,X0_52,X1_52) = k4_lattices(sK5,X1_52,X0_52) ),
    inference(subtyping,[status(esa)],[c_340])).

cnf(c_838,plain,
    ( k4_lattices(sK5,X0_52,X1_52) = k4_lattices(sK5,X1_52,X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_660])).

cnf(c_1592,plain,
    ( k4_lattices(sK5,X0_52,sK8) = k4_lattices(sK5,sK8,X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_834,c_838])).

cnf(c_2170,plain,
    ( k4_lattices(sK5,sK7,sK8) = k4_lattices(sK5,sK8,sK7) ),
    inference(superposition,[status(thm)],[c_835,c_1592])).

cnf(c_1116,plain,
    ( k2_lattices(sK5,sK8,X0_52) = k4_lattices(sK5,sK8,X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_834,c_837])).

cnf(c_1580,plain,
    ( k2_lattices(sK5,sK8,sK7) = k4_lattices(sK5,sK8,sK7) ),
    inference(superposition,[status(thm)],[c_835,c_1116])).

cnf(c_2327,plain,
    ( k2_lattices(sK5,sK8,sK7) = k4_lattices(sK5,sK7,sK8) ),
    inference(demodulation,[status(thm)],[c_2170,c_1580])).

cnf(c_1593,plain,
    ( k4_lattices(sK5,X0_52,sK7) = k4_lattices(sK5,sK7,X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_835,c_838])).

cnf(c_2612,plain,
    ( k4_lattices(sK5,sK7,sK6) = k4_lattices(sK5,sK6,sK7) ),
    inference(superposition,[status(thm)],[c_836,c_1593])).

cnf(c_2171,plain,
    ( k4_lattices(sK5,sK8,sK6) = k4_lattices(sK5,sK6,sK8) ),
    inference(superposition,[status(thm)],[c_836,c_1592])).

cnf(c_21,negated_conjecture,
    ( k4_lattices(sK5,sK6,sK7) = k4_lattices(sK5,sK6,sK8) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_665,negated_conjecture,
    ( k4_lattices(sK5,sK6,sK7) = k4_lattices(sK5,sK6,sK8) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2460,plain,
    ( k4_lattices(sK5,sK8,sK6) = k4_lattices(sK5,sK6,sK7) ),
    inference(demodulation,[status(thm)],[c_2171,c_665])).

cnf(c_2616,plain,
    ( k4_lattices(sK5,sK7,sK6) = k4_lattices(sK5,sK8,sK6) ),
    inference(demodulation,[status(thm)],[c_2612,c_2460])).

cnf(c_1581,plain,
    ( k2_lattices(sK5,sK8,sK6) = k4_lattices(sK5,sK8,sK6) ),
    inference(superposition,[status(thm)],[c_836,c_1116])).

cnf(c_2695,plain,
    ( k2_lattices(sK5,sK8,sK6) = k4_lattices(sK5,sK7,sK6) ),
    inference(demodulation,[status(thm)],[c_2616,c_1581])).

cnf(c_1022,plain,
    ( k2_lattices(sK5,sK8,k1_lattices(sK5,sK8,X0_52)) = sK8
    | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_834,c_841])).

cnf(c_1049,plain,
    ( k2_lattices(sK5,sK8,k1_lattices(sK5,sK8,sK6)) = sK8 ),
    inference(superposition,[status(thm)],[c_836,c_1022])).

cnf(c_3116,plain,
    ( k2_lattices(sK5,sK8,k3_lattices(sK5,sK8,sK6)) = sK8 ),
    inference(demodulation,[status(thm)],[c_2836,c_1049])).

cnf(c_5564,plain,
    ( k2_lattices(sK5,sK8,k3_lattices(sK5,sK7,sK6)) = sK8 ),
    inference(light_normalisation,[status(thm)],[c_3116,c_4252])).

cnf(c_6183,plain,
    ( k1_lattices(sK5,k4_lattices(sK5,sK7,sK8),k4_lattices(sK5,sK7,sK6)) = sK8 ),
    inference(light_normalisation,[status(thm)],[c_4523,c_2327,c_2695,c_5564])).

cnf(c_8020,plain,
    ( sK8 = sK7 ),
    inference(light_normalisation,[status(thm)],[c_8018,c_1743,c_3349,c_4328,c_6183])).

cnf(c_19,negated_conjecture,
    ( sK7 != sK8 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_667,negated_conjecture,
    ( sK7 != sK8 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_8321,plain,
    ( sK7 != sK7 ),
    inference(demodulation,[status(thm)],[c_8020,c_667])).

cnf(c_8322,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_8321])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:00:50 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.76/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.76/1.00  
% 3.76/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.76/1.00  
% 3.76/1.00  ------  iProver source info
% 3.76/1.00  
% 3.76/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.76/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.76/1.00  git: non_committed_changes: false
% 3.76/1.00  git: last_make_outside_of_git: false
% 3.76/1.00  
% 3.76/1.00  ------ 
% 3.76/1.00  
% 3.76/1.00  ------ Input Options
% 3.76/1.00  
% 3.76/1.00  --out_options                           all
% 3.76/1.00  --tptp_safe_out                         true
% 3.76/1.00  --problem_path                          ""
% 3.76/1.00  --include_path                          ""
% 3.76/1.00  --clausifier                            res/vclausify_rel
% 3.76/1.00  --clausifier_options                    --mode clausify
% 3.76/1.00  --stdin                                 false
% 3.76/1.00  --stats_out                             all
% 3.76/1.00  
% 3.76/1.00  ------ General Options
% 3.76/1.00  
% 3.76/1.00  --fof                                   false
% 3.76/1.00  --time_out_real                         305.
% 3.76/1.00  --time_out_virtual                      -1.
% 3.76/1.00  --symbol_type_check                     false
% 3.76/1.00  --clausify_out                          false
% 3.76/1.00  --sig_cnt_out                           false
% 3.76/1.00  --trig_cnt_out                          false
% 3.76/1.00  --trig_cnt_out_tolerance                1.
% 3.76/1.00  --trig_cnt_out_sk_spl                   false
% 3.76/1.00  --abstr_cl_out                          false
% 3.76/1.00  
% 3.76/1.00  ------ Global Options
% 3.76/1.00  
% 3.76/1.00  --schedule                              default
% 3.76/1.00  --add_important_lit                     false
% 3.76/1.00  --prop_solver_per_cl                    1000
% 3.76/1.00  --min_unsat_core                        false
% 3.76/1.00  --soft_assumptions                      false
% 3.76/1.00  --soft_lemma_size                       3
% 3.76/1.00  --prop_impl_unit_size                   0
% 3.76/1.00  --prop_impl_unit                        []
% 3.76/1.00  --share_sel_clauses                     true
% 3.76/1.00  --reset_solvers                         false
% 3.76/1.00  --bc_imp_inh                            [conj_cone]
% 3.76/1.00  --conj_cone_tolerance                   3.
% 3.76/1.00  --extra_neg_conj                        none
% 3.76/1.00  --large_theory_mode                     true
% 3.76/1.00  --prolific_symb_bound                   200
% 3.76/1.00  --lt_threshold                          2000
% 3.76/1.00  --clause_weak_htbl                      true
% 3.76/1.00  --gc_record_bc_elim                     false
% 3.76/1.00  
% 3.76/1.00  ------ Preprocessing Options
% 3.76/1.00  
% 3.76/1.00  --preprocessing_flag                    true
% 3.76/1.00  --time_out_prep_mult                    0.1
% 3.76/1.00  --splitting_mode                        input
% 3.76/1.00  --splitting_grd                         true
% 3.76/1.00  --splitting_cvd                         false
% 3.76/1.00  --splitting_cvd_svl                     false
% 3.76/1.00  --splitting_nvd                         32
% 3.76/1.00  --sub_typing                            true
% 3.76/1.00  --prep_gs_sim                           true
% 3.76/1.00  --prep_unflatten                        true
% 3.76/1.00  --prep_res_sim                          true
% 3.76/1.00  --prep_upred                            true
% 3.76/1.00  --prep_sem_filter                       exhaustive
% 3.76/1.00  --prep_sem_filter_out                   false
% 3.76/1.00  --pred_elim                             true
% 3.76/1.00  --res_sim_input                         true
% 3.76/1.00  --eq_ax_congr_red                       true
% 3.76/1.00  --pure_diseq_elim                       true
% 3.76/1.00  --brand_transform                       false
% 3.76/1.00  --non_eq_to_eq                          false
% 3.76/1.00  --prep_def_merge                        true
% 3.76/1.00  --prep_def_merge_prop_impl              false
% 3.76/1.00  --prep_def_merge_mbd                    true
% 3.76/1.00  --prep_def_merge_tr_red                 false
% 3.76/1.00  --prep_def_merge_tr_cl                  false
% 3.76/1.00  --smt_preprocessing                     true
% 3.76/1.00  --smt_ac_axioms                         fast
% 3.76/1.00  --preprocessed_out                      false
% 3.76/1.00  --preprocessed_stats                    false
% 3.76/1.00  
% 3.76/1.00  ------ Abstraction refinement Options
% 3.76/1.00  
% 3.76/1.00  --abstr_ref                             []
% 3.76/1.00  --abstr_ref_prep                        false
% 3.76/1.00  --abstr_ref_until_sat                   false
% 3.76/1.00  --abstr_ref_sig_restrict                funpre
% 3.76/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.76/1.00  --abstr_ref_under                       []
% 3.76/1.00  
% 3.76/1.00  ------ SAT Options
% 3.76/1.00  
% 3.76/1.00  --sat_mode                              false
% 3.76/1.00  --sat_fm_restart_options                ""
% 3.76/1.00  --sat_gr_def                            false
% 3.76/1.00  --sat_epr_types                         true
% 3.76/1.00  --sat_non_cyclic_types                  false
% 3.76/1.00  --sat_finite_models                     false
% 3.76/1.00  --sat_fm_lemmas                         false
% 3.76/1.00  --sat_fm_prep                           false
% 3.76/1.00  --sat_fm_uc_incr                        true
% 3.76/1.00  --sat_out_model                         small
% 3.76/1.00  --sat_out_clauses                       false
% 3.76/1.00  
% 3.76/1.00  ------ QBF Options
% 3.76/1.00  
% 3.76/1.00  --qbf_mode                              false
% 3.76/1.00  --qbf_elim_univ                         false
% 3.76/1.00  --qbf_dom_inst                          none
% 3.76/1.00  --qbf_dom_pre_inst                      false
% 3.76/1.00  --qbf_sk_in                             false
% 3.76/1.00  --qbf_pred_elim                         true
% 3.76/1.00  --qbf_split                             512
% 3.76/1.00  
% 3.76/1.00  ------ BMC1 Options
% 3.76/1.00  
% 3.76/1.00  --bmc1_incremental                      false
% 3.76/1.00  --bmc1_axioms                           reachable_all
% 3.76/1.00  --bmc1_min_bound                        0
% 3.76/1.00  --bmc1_max_bound                        -1
% 3.76/1.00  --bmc1_max_bound_default                -1
% 3.76/1.00  --bmc1_symbol_reachability              true
% 3.76/1.00  --bmc1_property_lemmas                  false
% 3.76/1.00  --bmc1_k_induction                      false
% 3.76/1.00  --bmc1_non_equiv_states                 false
% 3.76/1.00  --bmc1_deadlock                         false
% 3.76/1.00  --bmc1_ucm                              false
% 3.76/1.00  --bmc1_add_unsat_core                   none
% 3.76/1.00  --bmc1_unsat_core_children              false
% 3.76/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.76/1.00  --bmc1_out_stat                         full
% 3.76/1.00  --bmc1_ground_init                      false
% 3.76/1.00  --bmc1_pre_inst_next_state              false
% 3.76/1.00  --bmc1_pre_inst_state                   false
% 3.76/1.00  --bmc1_pre_inst_reach_state             false
% 3.76/1.00  --bmc1_out_unsat_core                   false
% 3.76/1.00  --bmc1_aig_witness_out                  false
% 3.76/1.00  --bmc1_verbose                          false
% 3.76/1.00  --bmc1_dump_clauses_tptp                false
% 3.76/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.76/1.00  --bmc1_dump_file                        -
% 3.76/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.76/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.76/1.00  --bmc1_ucm_extend_mode                  1
% 3.76/1.00  --bmc1_ucm_init_mode                    2
% 3.76/1.00  --bmc1_ucm_cone_mode                    none
% 3.76/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.76/1.00  --bmc1_ucm_relax_model                  4
% 3.76/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.76/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.76/1.00  --bmc1_ucm_layered_model                none
% 3.76/1.00  --bmc1_ucm_max_lemma_size               10
% 3.76/1.00  
% 3.76/1.00  ------ AIG Options
% 3.76/1.00  
% 3.76/1.00  --aig_mode                              false
% 3.76/1.00  
% 3.76/1.00  ------ Instantiation Options
% 3.76/1.00  
% 3.76/1.00  --instantiation_flag                    true
% 3.76/1.00  --inst_sos_flag                         false
% 3.76/1.00  --inst_sos_phase                        true
% 3.76/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.76/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.76/1.00  --inst_lit_sel_side                     num_symb
% 3.76/1.00  --inst_solver_per_active                1400
% 3.76/1.00  --inst_solver_calls_frac                1.
% 3.76/1.00  --inst_passive_queue_type               priority_queues
% 3.76/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.76/1.00  --inst_passive_queues_freq              [25;2]
% 3.76/1.00  --inst_dismatching                      true
% 3.76/1.00  --inst_eager_unprocessed_to_passive     true
% 3.76/1.00  --inst_prop_sim_given                   true
% 3.76/1.00  --inst_prop_sim_new                     false
% 3.76/1.00  --inst_subs_new                         false
% 3.76/1.00  --inst_eq_res_simp                      false
% 3.76/1.00  --inst_subs_given                       false
% 3.76/1.00  --inst_orphan_elimination               true
% 3.76/1.00  --inst_learning_loop_flag               true
% 3.76/1.00  --inst_learning_start                   3000
% 3.76/1.00  --inst_learning_factor                  2
% 3.76/1.00  --inst_start_prop_sim_after_learn       3
% 3.76/1.00  --inst_sel_renew                        solver
% 3.76/1.00  --inst_lit_activity_flag                true
% 3.76/1.00  --inst_restr_to_given                   false
% 3.76/1.00  --inst_activity_threshold               500
% 3.76/1.00  --inst_out_proof                        true
% 3.76/1.00  
% 3.76/1.00  ------ Resolution Options
% 3.76/1.00  
% 3.76/1.00  --resolution_flag                       true
% 3.76/1.00  --res_lit_sel                           adaptive
% 3.76/1.00  --res_lit_sel_side                      none
% 3.76/1.00  --res_ordering                          kbo
% 3.76/1.00  --res_to_prop_solver                    active
% 3.76/1.00  --res_prop_simpl_new                    false
% 3.76/1.00  --res_prop_simpl_given                  true
% 3.76/1.00  --res_passive_queue_type                priority_queues
% 3.76/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.76/1.00  --res_passive_queues_freq               [15;5]
% 3.76/1.00  --res_forward_subs                      full
% 3.76/1.00  --res_backward_subs                     full
% 3.76/1.00  --res_forward_subs_resolution           true
% 3.76/1.00  --res_backward_subs_resolution          true
% 3.76/1.00  --res_orphan_elimination                true
% 3.76/1.00  --res_time_limit                        2.
% 3.76/1.00  --res_out_proof                         true
% 3.76/1.00  
% 3.76/1.00  ------ Superposition Options
% 3.76/1.00  
% 3.76/1.00  --superposition_flag                    true
% 3.76/1.00  --sup_passive_queue_type                priority_queues
% 3.76/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.76/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.76/1.00  --demod_completeness_check              fast
% 3.76/1.00  --demod_use_ground                      true
% 3.76/1.00  --sup_to_prop_solver                    passive
% 3.76/1.00  --sup_prop_simpl_new                    true
% 3.76/1.00  --sup_prop_simpl_given                  true
% 3.76/1.00  --sup_fun_splitting                     false
% 3.76/1.00  --sup_smt_interval                      50000
% 3.76/1.00  
% 3.76/1.00  ------ Superposition Simplification Setup
% 3.76/1.00  
% 3.76/1.00  --sup_indices_passive                   []
% 3.76/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.76/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/1.00  --sup_full_bw                           [BwDemod]
% 3.76/1.00  --sup_immed_triv                        [TrivRules]
% 3.76/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/1.00  --sup_immed_bw_main                     []
% 3.76/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.76/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.76/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.76/1.00  
% 3.76/1.00  ------ Combination Options
% 3.76/1.00  
% 3.76/1.00  --comb_res_mult                         3
% 3.76/1.00  --comb_sup_mult                         2
% 3.76/1.00  --comb_inst_mult                        10
% 3.76/1.00  
% 3.76/1.00  ------ Debug Options
% 3.76/1.00  
% 3.76/1.00  --dbg_backtrace                         false
% 3.76/1.00  --dbg_dump_prop_clauses                 false
% 3.76/1.00  --dbg_dump_prop_clauses_file            -
% 3.76/1.00  --dbg_out_stat                          false
% 3.76/1.00  ------ Parsing...
% 3.76/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.76/1.00  
% 3.76/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.76/1.00  
% 3.76/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.76/1.00  
% 3.76/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.76/1.00  ------ Proving...
% 3.76/1.00  ------ Problem Properties 
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  clauses                                 12
% 3.76/1.00  conjectures                             6
% 3.76/1.00  EPR                                     1
% 3.76/1.00  Horn                                    12
% 3.76/1.00  unary                                   6
% 3.76/1.00  binary                                  0
% 3.76/1.00  lits                                    25
% 3.76/1.00  lits eq                                 9
% 3.76/1.00  fd_pure                                 0
% 3.76/1.00  fd_pseudo                               0
% 3.76/1.00  fd_cond                                 0
% 3.76/1.00  fd_pseudo_cond                          0
% 3.76/1.00  AC symbols                              0
% 3.76/1.00  
% 3.76/1.00  ------ Schedule dynamic 5 is on 
% 3.76/1.00  
% 3.76/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  ------ 
% 3.76/1.00  Current options:
% 3.76/1.00  ------ 
% 3.76/1.00  
% 3.76/1.00  ------ Input Options
% 3.76/1.00  
% 3.76/1.00  --out_options                           all
% 3.76/1.00  --tptp_safe_out                         true
% 3.76/1.00  --problem_path                          ""
% 3.76/1.00  --include_path                          ""
% 3.76/1.00  --clausifier                            res/vclausify_rel
% 3.76/1.00  --clausifier_options                    --mode clausify
% 3.76/1.00  --stdin                                 false
% 3.76/1.00  --stats_out                             all
% 3.76/1.00  
% 3.76/1.00  ------ General Options
% 3.76/1.00  
% 3.76/1.00  --fof                                   false
% 3.76/1.00  --time_out_real                         305.
% 3.76/1.00  --time_out_virtual                      -1.
% 3.76/1.00  --symbol_type_check                     false
% 3.76/1.00  --clausify_out                          false
% 3.76/1.00  --sig_cnt_out                           false
% 3.76/1.00  --trig_cnt_out                          false
% 3.76/1.00  --trig_cnt_out_tolerance                1.
% 3.76/1.00  --trig_cnt_out_sk_spl                   false
% 3.76/1.00  --abstr_cl_out                          false
% 3.76/1.00  
% 3.76/1.00  ------ Global Options
% 3.76/1.00  
% 3.76/1.00  --schedule                              default
% 3.76/1.00  --add_important_lit                     false
% 3.76/1.00  --prop_solver_per_cl                    1000
% 3.76/1.00  --min_unsat_core                        false
% 3.76/1.00  --soft_assumptions                      false
% 3.76/1.00  --soft_lemma_size                       3
% 3.76/1.00  --prop_impl_unit_size                   0
% 3.76/1.00  --prop_impl_unit                        []
% 3.76/1.00  --share_sel_clauses                     true
% 3.76/1.00  --reset_solvers                         false
% 3.76/1.00  --bc_imp_inh                            [conj_cone]
% 3.76/1.00  --conj_cone_tolerance                   3.
% 3.76/1.00  --extra_neg_conj                        none
% 3.76/1.00  --large_theory_mode                     true
% 3.76/1.00  --prolific_symb_bound                   200
% 3.76/1.00  --lt_threshold                          2000
% 3.76/1.00  --clause_weak_htbl                      true
% 3.76/1.00  --gc_record_bc_elim                     false
% 3.76/1.00  
% 3.76/1.00  ------ Preprocessing Options
% 3.76/1.00  
% 3.76/1.00  --preprocessing_flag                    true
% 3.76/1.00  --time_out_prep_mult                    0.1
% 3.76/1.00  --splitting_mode                        input
% 3.76/1.00  --splitting_grd                         true
% 3.76/1.00  --splitting_cvd                         false
% 3.76/1.00  --splitting_cvd_svl                     false
% 3.76/1.00  --splitting_nvd                         32
% 3.76/1.00  --sub_typing                            true
% 3.76/1.00  --prep_gs_sim                           true
% 3.76/1.00  --prep_unflatten                        true
% 3.76/1.00  --prep_res_sim                          true
% 3.76/1.00  --prep_upred                            true
% 3.76/1.00  --prep_sem_filter                       exhaustive
% 3.76/1.00  --prep_sem_filter_out                   false
% 3.76/1.00  --pred_elim                             true
% 3.76/1.00  --res_sim_input                         true
% 3.76/1.00  --eq_ax_congr_red                       true
% 3.76/1.00  --pure_diseq_elim                       true
% 3.76/1.00  --brand_transform                       false
% 3.76/1.00  --non_eq_to_eq                          false
% 3.76/1.00  --prep_def_merge                        true
% 3.76/1.00  --prep_def_merge_prop_impl              false
% 3.76/1.00  --prep_def_merge_mbd                    true
% 3.76/1.00  --prep_def_merge_tr_red                 false
% 3.76/1.00  --prep_def_merge_tr_cl                  false
% 3.76/1.00  --smt_preprocessing                     true
% 3.76/1.00  --smt_ac_axioms                         fast
% 3.76/1.00  --preprocessed_out                      false
% 3.76/1.00  --preprocessed_stats                    false
% 3.76/1.00  
% 3.76/1.00  ------ Abstraction refinement Options
% 3.76/1.00  
% 3.76/1.00  --abstr_ref                             []
% 3.76/1.00  --abstr_ref_prep                        false
% 3.76/1.00  --abstr_ref_until_sat                   false
% 3.76/1.00  --abstr_ref_sig_restrict                funpre
% 3.76/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.76/1.00  --abstr_ref_under                       []
% 3.76/1.00  
% 3.76/1.00  ------ SAT Options
% 3.76/1.00  
% 3.76/1.00  --sat_mode                              false
% 3.76/1.00  --sat_fm_restart_options                ""
% 3.76/1.00  --sat_gr_def                            false
% 3.76/1.00  --sat_epr_types                         true
% 3.76/1.00  --sat_non_cyclic_types                  false
% 3.76/1.00  --sat_finite_models                     false
% 3.76/1.00  --sat_fm_lemmas                         false
% 3.76/1.00  --sat_fm_prep                           false
% 3.76/1.00  --sat_fm_uc_incr                        true
% 3.76/1.00  --sat_out_model                         small
% 3.76/1.00  --sat_out_clauses                       false
% 3.76/1.00  
% 3.76/1.00  ------ QBF Options
% 3.76/1.00  
% 3.76/1.00  --qbf_mode                              false
% 3.76/1.00  --qbf_elim_univ                         false
% 3.76/1.00  --qbf_dom_inst                          none
% 3.76/1.00  --qbf_dom_pre_inst                      false
% 3.76/1.00  --qbf_sk_in                             false
% 3.76/1.00  --qbf_pred_elim                         true
% 3.76/1.00  --qbf_split                             512
% 3.76/1.00  
% 3.76/1.00  ------ BMC1 Options
% 3.76/1.00  
% 3.76/1.00  --bmc1_incremental                      false
% 3.76/1.00  --bmc1_axioms                           reachable_all
% 3.76/1.00  --bmc1_min_bound                        0
% 3.76/1.00  --bmc1_max_bound                        -1
% 3.76/1.00  --bmc1_max_bound_default                -1
% 3.76/1.00  --bmc1_symbol_reachability              true
% 3.76/1.00  --bmc1_property_lemmas                  false
% 3.76/1.00  --bmc1_k_induction                      false
% 3.76/1.00  --bmc1_non_equiv_states                 false
% 3.76/1.00  --bmc1_deadlock                         false
% 3.76/1.00  --bmc1_ucm                              false
% 3.76/1.00  --bmc1_add_unsat_core                   none
% 3.76/1.00  --bmc1_unsat_core_children              false
% 3.76/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.76/1.00  --bmc1_out_stat                         full
% 3.76/1.00  --bmc1_ground_init                      false
% 3.76/1.00  --bmc1_pre_inst_next_state              false
% 3.76/1.00  --bmc1_pre_inst_state                   false
% 3.76/1.00  --bmc1_pre_inst_reach_state             false
% 3.76/1.00  --bmc1_out_unsat_core                   false
% 3.76/1.00  --bmc1_aig_witness_out                  false
% 3.76/1.00  --bmc1_verbose                          false
% 3.76/1.00  --bmc1_dump_clauses_tptp                false
% 3.76/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.76/1.00  --bmc1_dump_file                        -
% 3.76/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.76/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.76/1.00  --bmc1_ucm_extend_mode                  1
% 3.76/1.00  --bmc1_ucm_init_mode                    2
% 3.76/1.00  --bmc1_ucm_cone_mode                    none
% 3.76/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.76/1.00  --bmc1_ucm_relax_model                  4
% 3.76/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.76/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.76/1.00  --bmc1_ucm_layered_model                none
% 3.76/1.00  --bmc1_ucm_max_lemma_size               10
% 3.76/1.00  
% 3.76/1.00  ------ AIG Options
% 3.76/1.00  
% 3.76/1.00  --aig_mode                              false
% 3.76/1.00  
% 3.76/1.00  ------ Instantiation Options
% 3.76/1.00  
% 3.76/1.00  --instantiation_flag                    true
% 3.76/1.00  --inst_sos_flag                         false
% 3.76/1.00  --inst_sos_phase                        true
% 3.76/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.76/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.76/1.00  --inst_lit_sel_side                     none
% 3.76/1.00  --inst_solver_per_active                1400
% 3.76/1.00  --inst_solver_calls_frac                1.
% 3.76/1.00  --inst_passive_queue_type               priority_queues
% 3.76/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.76/1.00  --inst_passive_queues_freq              [25;2]
% 3.76/1.00  --inst_dismatching                      true
% 3.76/1.00  --inst_eager_unprocessed_to_passive     true
% 3.76/1.00  --inst_prop_sim_given                   true
% 3.76/1.00  --inst_prop_sim_new                     false
% 3.76/1.00  --inst_subs_new                         false
% 3.76/1.00  --inst_eq_res_simp                      false
% 3.76/1.00  --inst_subs_given                       false
% 3.76/1.00  --inst_orphan_elimination               true
% 3.76/1.00  --inst_learning_loop_flag               true
% 3.76/1.00  --inst_learning_start                   3000
% 3.76/1.00  --inst_learning_factor                  2
% 3.76/1.00  --inst_start_prop_sim_after_learn       3
% 3.76/1.00  --inst_sel_renew                        solver
% 3.76/1.00  --inst_lit_activity_flag                true
% 3.76/1.00  --inst_restr_to_given                   false
% 3.76/1.00  --inst_activity_threshold               500
% 3.76/1.00  --inst_out_proof                        true
% 3.76/1.00  
% 3.76/1.00  ------ Resolution Options
% 3.76/1.00  
% 3.76/1.00  --resolution_flag                       false
% 3.76/1.00  --res_lit_sel                           adaptive
% 3.76/1.00  --res_lit_sel_side                      none
% 3.76/1.00  --res_ordering                          kbo
% 3.76/1.00  --res_to_prop_solver                    active
% 3.76/1.00  --res_prop_simpl_new                    false
% 3.76/1.00  --res_prop_simpl_given                  true
% 3.76/1.00  --res_passive_queue_type                priority_queues
% 3.76/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.76/1.00  --res_passive_queues_freq               [15;5]
% 3.76/1.00  --res_forward_subs                      full
% 3.76/1.00  --res_backward_subs                     full
% 3.76/1.00  --res_forward_subs_resolution           true
% 3.76/1.00  --res_backward_subs_resolution          true
% 3.76/1.00  --res_orphan_elimination                true
% 3.76/1.00  --res_time_limit                        2.
% 3.76/1.00  --res_out_proof                         true
% 3.76/1.00  
% 3.76/1.00  ------ Superposition Options
% 3.76/1.00  
% 3.76/1.00  --superposition_flag                    true
% 3.76/1.00  --sup_passive_queue_type                priority_queues
% 3.76/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.76/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.76/1.00  --demod_completeness_check              fast
% 3.76/1.00  --demod_use_ground                      true
% 3.76/1.00  --sup_to_prop_solver                    passive
% 3.76/1.00  --sup_prop_simpl_new                    true
% 3.76/1.00  --sup_prop_simpl_given                  true
% 3.76/1.00  --sup_fun_splitting                     false
% 3.76/1.00  --sup_smt_interval                      50000
% 3.76/1.00  
% 3.76/1.00  ------ Superposition Simplification Setup
% 3.76/1.00  
% 3.76/1.00  --sup_indices_passive                   []
% 3.76/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.76/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/1.00  --sup_full_bw                           [BwDemod]
% 3.76/1.00  --sup_immed_triv                        [TrivRules]
% 3.76/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/1.00  --sup_immed_bw_main                     []
% 3.76/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.76/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.76/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.76/1.00  
% 3.76/1.00  ------ Combination Options
% 3.76/1.00  
% 3.76/1.00  --comb_res_mult                         3
% 3.76/1.00  --comb_sup_mult                         2
% 3.76/1.00  --comb_inst_mult                        10
% 3.76/1.00  
% 3.76/1.00  ------ Debug Options
% 3.76/1.00  
% 3.76/1.00  --dbg_backtrace                         false
% 3.76/1.00  --dbg_dump_prop_clauses                 false
% 3.76/1.00  --dbg_dump_prop_clauses_file            -
% 3.76/1.00  --dbg_out_stat                          false
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  ------ Proving...
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  % SZS status Theorem for theBenchmark.p
% 3.76/1.00  
% 3.76/1.00   Resolution empty clause
% 3.76/1.00  
% 3.76/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.76/1.00  
% 3.76/1.00  fof(f9,conjecture,(
% 3.76/1.00    ! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 3.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f10,negated_conjecture,(
% 3.76/1.00    ~! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 3.76/1.00    inference(negated_conjecture,[],[f9])).
% 3.76/1.00  
% 3.76/1.00  fof(f29,plain,(
% 3.76/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((X2 != X3 & (k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 3.76/1.00    inference(ennf_transformation,[],[f10])).
% 3.76/1.00  
% 3.76/1.00  fof(f30,plain,(
% 3.76/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 3.76/1.00    inference(flattening,[],[f29])).
% 3.76/1.00  
% 3.76/1.00  fof(f45,plain,(
% 3.76/1.00    ( ! [X2,X0,X1] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (sK8 != X2 & k3_lattices(X0,X1,sK8) = k3_lattices(X0,X1,X2) & k4_lattices(X0,X1,sK8) = k4_lattices(X0,X1,X2) & m1_subset_1(sK8,u1_struct_0(X0)))) )),
% 3.76/1.00    introduced(choice_axiom,[])).
% 3.76/1.00  
% 3.76/1.00  fof(f44,plain,(
% 3.76/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (sK7 != X3 & k3_lattices(X0,X1,sK7) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,sK7) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK7,u1_struct_0(X0)))) )),
% 3.76/1.00    introduced(choice_axiom,[])).
% 3.76/1.00  
% 3.76/1.00  fof(f43,plain,(
% 3.76/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,sK6,X2) = k3_lattices(X0,sK6,X3) & k4_lattices(X0,sK6,X2) = k4_lattices(X0,sK6,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 3.76/1.00    introduced(choice_axiom,[])).
% 3.76/1.00  
% 3.76/1.00  fof(f42,plain,(
% 3.76/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(sK5,X1,X2) = k3_lattices(sK5,X1,X3) & k4_lattices(sK5,X1,X2) = k4_lattices(sK5,X1,X3) & m1_subset_1(X3,u1_struct_0(sK5))) & m1_subset_1(X2,u1_struct_0(sK5))) & m1_subset_1(X1,u1_struct_0(sK5))) & l3_lattices(sK5) & v11_lattices(sK5) & v10_lattices(sK5) & ~v2_struct_0(sK5))),
% 3.76/1.00    introduced(choice_axiom,[])).
% 3.76/1.00  
% 3.76/1.00  fof(f46,plain,(
% 3.76/1.00    (((sK7 != sK8 & k3_lattices(sK5,sK6,sK7) = k3_lattices(sK5,sK6,sK8) & k4_lattices(sK5,sK6,sK7) = k4_lattices(sK5,sK6,sK8) & m1_subset_1(sK8,u1_struct_0(sK5))) & m1_subset_1(sK7,u1_struct_0(sK5))) & m1_subset_1(sK6,u1_struct_0(sK5))) & l3_lattices(sK5) & v11_lattices(sK5) & v10_lattices(sK5) & ~v2_struct_0(sK5)),
% 3.76/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f30,f45,f44,f43,f42])).
% 3.76/1.00  
% 3.76/1.00  fof(f70,plain,(
% 3.76/1.00    m1_subset_1(sK6,u1_struct_0(sK5))),
% 3.76/1.00    inference(cnf_transformation,[],[f46])).
% 3.76/1.00  
% 3.76/1.00  fof(f72,plain,(
% 3.76/1.00    m1_subset_1(sK8,u1_struct_0(sK5))),
% 3.76/1.00    inference(cnf_transformation,[],[f46])).
% 3.76/1.00  
% 3.76/1.00  fof(f71,plain,(
% 3.76/1.00    m1_subset_1(sK7,u1_struct_0(sK5))),
% 3.76/1.00    inference(cnf_transformation,[],[f46])).
% 3.76/1.00  
% 3.76/1.00  fof(f4,axiom,(
% 3.76/1.00    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v11_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3)))))))),
% 3.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f20,plain,(
% 3.76/1.00    ! [X0] : ((v11_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.76/1.00    inference(ennf_transformation,[],[f4])).
% 3.76/1.00  
% 3.76/1.00  fof(f21,plain,(
% 3.76/1.00    ! [X0] : ((v11_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(flattening,[],[f20])).
% 3.76/1.00  
% 3.76/1.00  fof(f31,plain,(
% 3.76/1.00    ! [X0] : (((v11_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (! [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(nnf_transformation,[],[f21])).
% 3.76/1.00  
% 3.76/1.00  fof(f32,plain,(
% 3.76/1.00    ! [X0] : (((v11_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(rectify,[],[f31])).
% 3.76/1.00  
% 3.76/1.00  fof(f35,plain,(
% 3.76/1.00    ( ! [X2,X1] : (! [X0] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) => (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,sK2(X0))) != k2_lattices(X0,X1,k1_lattices(X0,X2,sK2(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))) )),
% 3.76/1.00    introduced(choice_axiom,[])).
% 3.76/1.00  
% 3.76/1.00  fof(f34,plain,(
% 3.76/1.00    ( ! [X1] : (! [X0] : (? [X2] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,sK1(X0)),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,sK1(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK1(X0),u1_struct_0(X0))))) )),
% 3.76/1.00    introduced(choice_axiom,[])).
% 3.76/1.00  
% 3.76/1.00  fof(f33,plain,(
% 3.76/1.00    ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,sK0(X0),X2),k2_lattices(X0,sK0(X0),X3)) != k2_lattices(X0,sK0(X0),k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0))))),
% 3.76/1.00    introduced(choice_axiom,[])).
% 3.76/1.00  
% 3.76/1.00  fof(f36,plain,(
% 3.76/1.00    ! [X0] : (((v11_lattices(X0) | (((k1_lattices(X0,k2_lattices(X0,sK0(X0),sK1(X0)),k2_lattices(X0,sK0(X0),sK2(X0))) != k2_lattices(X0,sK0(X0),k1_lattices(X0,sK1(X0),sK2(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))) & m1_subset_1(sK1(X0),u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f35,f34,f33])).
% 3.76/1.00  
% 3.76/1.00  fof(f53,plain,(
% 3.76/1.00    ( ! [X6,X4,X0,X5] : (k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v11_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f36])).
% 3.76/1.00  
% 3.76/1.00  fof(f66,plain,(
% 3.76/1.00    ~v2_struct_0(sK5)),
% 3.76/1.00    inference(cnf_transformation,[],[f46])).
% 3.76/1.00  
% 3.76/1.00  fof(f68,plain,(
% 3.76/1.00    v11_lattices(sK5)),
% 3.76/1.00    inference(cnf_transformation,[],[f46])).
% 3.76/1.00  
% 3.76/1.00  fof(f69,plain,(
% 3.76/1.00    l3_lattices(sK5)),
% 3.76/1.00    inference(cnf_transformation,[],[f46])).
% 3.76/1.00  
% 3.76/1.00  fof(f8,axiom,(
% 3.76/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 3.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f27,plain,(
% 3.76/1.00    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.76/1.00    inference(ennf_transformation,[],[f8])).
% 3.76/1.00  
% 3.76/1.00  fof(f28,plain,(
% 3.76/1.00    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(flattening,[],[f27])).
% 3.76/1.00  
% 3.76/1.00  fof(f65,plain,(
% 3.76/1.00    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f28])).
% 3.76/1.00  
% 3.76/1.00  fof(f1,axiom,(
% 3.76/1.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f11,plain,(
% 3.76/1.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.76/1.00    inference(pure_predicate_removal,[],[f1])).
% 3.76/1.00  
% 3.76/1.00  fof(f12,plain,(
% 3.76/1.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.76/1.00    inference(pure_predicate_removal,[],[f11])).
% 3.76/1.00  
% 3.76/1.00  fof(f13,plain,(
% 3.76/1.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.76/1.00    inference(pure_predicate_removal,[],[f12])).
% 3.76/1.00  
% 3.76/1.00  fof(f14,plain,(
% 3.76/1.00    ! [X0] : (((v9_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 3.76/1.00    inference(ennf_transformation,[],[f13])).
% 3.76/1.00  
% 3.76/1.00  fof(f15,plain,(
% 3.76/1.00    ! [X0] : ((v9_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 3.76/1.00    inference(flattening,[],[f14])).
% 3.76/1.00  
% 3.76/1.00  fof(f49,plain,(
% 3.76/1.00    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f15])).
% 3.76/1.00  
% 3.76/1.00  fof(f67,plain,(
% 3.76/1.00    v10_lattices(sK5)),
% 3.76/1.00    inference(cnf_transformation,[],[f46])).
% 3.76/1.00  
% 3.76/1.00  fof(f6,axiom,(
% 3.76/1.00    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 3.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f24,plain,(
% 3.76/1.00    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 3.76/1.00    inference(ennf_transformation,[],[f6])).
% 3.76/1.00  
% 3.76/1.00  fof(f62,plain,(
% 3.76/1.00    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f24])).
% 3.76/1.00  
% 3.76/1.00  fof(f7,axiom,(
% 3.76/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 3.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f25,plain,(
% 3.76/1.00    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 3.76/1.00    inference(ennf_transformation,[],[f7])).
% 3.76/1.00  
% 3.76/1.00  fof(f26,plain,(
% 3.76/1.00    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(flattening,[],[f25])).
% 3.76/1.00  
% 3.76/1.00  fof(f64,plain,(
% 3.76/1.00    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f26])).
% 3.76/1.00  
% 3.76/1.00  fof(f48,plain,(
% 3.76/1.00    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f15])).
% 3.76/1.00  
% 3.76/1.00  fof(f63,plain,(
% 3.76/1.00    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f24])).
% 3.76/1.00  
% 3.76/1.00  fof(f5,axiom,(
% 3.76/1.00    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 3.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f22,plain,(
% 3.76/1.00    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.76/1.00    inference(ennf_transformation,[],[f5])).
% 3.76/1.00  
% 3.76/1.00  fof(f23,plain,(
% 3.76/1.00    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(flattening,[],[f22])).
% 3.76/1.00  
% 3.76/1.00  fof(f37,plain,(
% 3.76/1.00    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(nnf_transformation,[],[f23])).
% 3.76/1.00  
% 3.76/1.00  fof(f38,plain,(
% 3.76/1.00    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(rectify,[],[f37])).
% 3.76/1.00  
% 3.76/1.00  fof(f40,plain,(
% 3.76/1.00    ( ! [X1] : (! [X0] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,X1,k1_lattices(X0,X1,sK4(X0))) != X1 & m1_subset_1(sK4(X0),u1_struct_0(X0))))) )),
% 3.76/1.00    introduced(choice_axiom,[])).
% 3.76/1.00  
% 3.76/1.00  fof(f39,plain,(
% 3.76/1.00    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK3(X0),k1_lattices(X0,sK3(X0),X2)) != sK3(X0) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 3.76/1.00    introduced(choice_axiom,[])).
% 3.76/1.00  
% 3.76/1.00  fof(f41,plain,(
% 3.76/1.00    ! [X0] : (((v9_lattices(X0) | ((k2_lattices(X0,sK3(X0),k1_lattices(X0,sK3(X0),sK4(X0))) != sK3(X0) & m1_subset_1(sK4(X0),u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f38,f40,f39])).
% 3.76/1.00  
% 3.76/1.00  fof(f58,plain,(
% 3.76/1.00    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v9_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f41])).
% 3.76/1.00  
% 3.76/1.00  fof(f50,plain,(
% 3.76/1.00    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f15])).
% 3.76/1.00  
% 3.76/1.00  fof(f2,axiom,(
% 3.76/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 3.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f16,plain,(
% 3.76/1.00    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 3.76/1.00    inference(ennf_transformation,[],[f2])).
% 3.76/1.00  
% 3.76/1.00  fof(f17,plain,(
% 3.76/1.00    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(flattening,[],[f16])).
% 3.76/1.00  
% 3.76/1.00  fof(f51,plain,(
% 3.76/1.00    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f17])).
% 3.76/1.00  
% 3.76/1.00  fof(f74,plain,(
% 3.76/1.00    k3_lattices(sK5,sK6,sK7) = k3_lattices(sK5,sK6,sK8)),
% 3.76/1.00    inference(cnf_transformation,[],[f46])).
% 3.76/1.00  
% 3.76/1.00  fof(f3,axiom,(
% 3.76/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 3.76/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f18,plain,(
% 3.76/1.00    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.76/1.00    inference(ennf_transformation,[],[f3])).
% 3.76/1.00  
% 3.76/1.00  fof(f19,plain,(
% 3.76/1.00    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(flattening,[],[f18])).
% 3.76/1.00  
% 3.76/1.00  fof(f52,plain,(
% 3.76/1.00    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f19])).
% 3.76/1.00  
% 3.76/1.00  fof(f73,plain,(
% 3.76/1.00    k4_lattices(sK5,sK6,sK7) = k4_lattices(sK5,sK6,sK8)),
% 3.76/1.00    inference(cnf_transformation,[],[f46])).
% 3.76/1.00  
% 3.76/1.00  fof(f75,plain,(
% 3.76/1.00    sK7 != sK8),
% 3.76/1.00    inference(cnf_transformation,[],[f46])).
% 3.76/1.00  
% 3.76/1.00  cnf(c_24,negated_conjecture,
% 3.76/1.00      ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 3.76/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_662,negated_conjecture,
% 3.76/1.00      ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_24]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_836,plain,
% 3.76/1.00      ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_662]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_22,negated_conjecture,
% 3.76/1.00      ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
% 3.76/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_664,negated_conjecture,
% 3.76/1.00      ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_834,plain,
% 3.76/1.00      ( m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_664]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_23,negated_conjecture,
% 3.76/1.00      ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 3.76/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_663,negated_conjecture,
% 3.76/1.00      ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_23]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_835,plain,
% 3.76/1.00      ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_663]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_10,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.76/1.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.76/1.00      | ~ v11_lattices(X1)
% 3.76/1.00      | ~ l3_lattices(X1)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0)) ),
% 3.76/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_28,negated_conjecture,
% 3.76/1.00      ( ~ v2_struct_0(sK5) ),
% 3.76/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_560,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.76/1.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.76/1.00      | ~ v11_lattices(X1)
% 3.76/1.00      | ~ l3_lattices(X1)
% 3.76/1.00      | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0))
% 3.76/1.00      | sK5 != X1 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_28]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_561,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 3.76/1.00      | ~ v11_lattices(sK5)
% 3.76/1.00      | ~ l3_lattices(sK5)
% 3.76/1.00      | k1_lattices(sK5,k2_lattices(sK5,X2,X0),k2_lattices(sK5,X2,X1)) = k2_lattices(sK5,X2,k1_lattices(sK5,X0,X1)) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_560]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_26,negated_conjecture,
% 3.76/1.00      ( v11_lattices(sK5) ),
% 3.76/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_25,negated_conjecture,
% 3.76/1.00      ( l3_lattices(sK5) ),
% 3.76/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_565,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 3.76/1.00      | k1_lattices(sK5,k2_lattices(sK5,X2,X0),k2_lattices(sK5,X2,X1)) = k2_lattices(sK5,X2,k1_lattices(sK5,X0,X1)) ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_561,c_26,c_25]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_566,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 3.76/1.00      | k1_lattices(sK5,k2_lattices(sK5,X0,X1),k2_lattices(sK5,X0,X2)) = k2_lattices(sK5,X0,k1_lattices(sK5,X1,X2)) ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_565]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_656,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0_52,u1_struct_0(sK5))
% 3.76/1.00      | ~ m1_subset_1(X1_52,u1_struct_0(sK5))
% 3.76/1.00      | ~ m1_subset_1(X2_52,u1_struct_0(sK5))
% 3.76/1.00      | k1_lattices(sK5,k2_lattices(sK5,X0_52,X1_52),k2_lattices(sK5,X0_52,X2_52)) = k2_lattices(sK5,X0_52,k1_lattices(sK5,X1_52,X2_52)) ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_566]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_842,plain,
% 3.76/1.00      ( k1_lattices(sK5,k2_lattices(sK5,X0_52,X1_52),k2_lattices(sK5,X0_52,X2_52)) = k2_lattices(sK5,X0_52,k1_lattices(sK5,X1_52,X2_52))
% 3.76/1.00      | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top
% 3.76/1.00      | m1_subset_1(X1_52,u1_struct_0(sK5)) != iProver_top
% 3.76/1.00      | m1_subset_1(X2_52,u1_struct_0(sK5)) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_656]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3911,plain,
% 3.76/1.00      ( k1_lattices(sK5,k2_lattices(sK5,sK7,X0_52),k2_lattices(sK5,sK7,X1_52)) = k2_lattices(sK5,sK7,k1_lattices(sK5,X0_52,X1_52))
% 3.76/1.00      | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top
% 3.76/1.00      | m1_subset_1(X1_52,u1_struct_0(sK5)) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_835,c_842]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_4633,plain,
% 3.76/1.00      ( k1_lattices(sK5,k2_lattices(sK5,sK7,sK8),k2_lattices(sK5,sK7,X0_52)) = k2_lattices(sK5,sK7,k1_lattices(sK5,sK8,X0_52))
% 3.76/1.00      | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_834,c_3911]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_18,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.76/1.00      | ~ l1_lattices(X1)
% 3.76/1.00      | ~ v6_lattices(X1)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1,plain,
% 3.76/1.00      ( v6_lattices(X0)
% 3.76/1.00      | ~ l3_lattices(X0)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v10_lattices(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_27,negated_conjecture,
% 3.76/1.00      ( v10_lattices(sK5) ),
% 3.76/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_286,plain,
% 3.76/1.00      ( v6_lattices(X0) | ~ l3_lattices(X0) | v2_struct_0(X0) | sK5 != X0 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_27]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_287,plain,
% 3.76/1.00      ( v6_lattices(sK5) | ~ l3_lattices(sK5) | v2_struct_0(sK5) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_286]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_78,plain,
% 3.76/1.00      ( v6_lattices(sK5)
% 3.76/1.00      | ~ l3_lattices(sK5)
% 3.76/1.00      | v2_struct_0(sK5)
% 3.76/1.00      | ~ v10_lattices(sK5) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_289,plain,
% 3.76/1.00      ( v6_lattices(sK5) ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_287,c_28,c_27,c_25,c_78]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_314,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.76/1.00      | ~ l1_lattices(X1)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0)
% 3.76/1.00      | sK5 != X1 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_289]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_315,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.76/1.00      | ~ l1_lattices(sK5)
% 3.76/1.00      | v2_struct_0(sK5)
% 3.76/1.00      | k2_lattices(sK5,X0,X1) = k4_lattices(sK5,X0,X1) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_314]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_16,plain,
% 3.76/1.00      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_43,plain,
% 3.76/1.00      ( l1_lattices(sK5) | ~ l3_lattices(sK5) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_319,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.76/1.00      | k2_lattices(sK5,X0,X1) = k4_lattices(sK5,X0,X1) ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_315,c_28,c_25,c_43]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_661,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0_52,u1_struct_0(sK5))
% 3.76/1.00      | ~ m1_subset_1(X1_52,u1_struct_0(sK5))
% 3.76/1.00      | k2_lattices(sK5,X0_52,X1_52) = k4_lattices(sK5,X0_52,X1_52) ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_319]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_837,plain,
% 3.76/1.00      ( k2_lattices(sK5,X0_52,X1_52) = k4_lattices(sK5,X0_52,X1_52)
% 3.76/1.00      | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top
% 3.76/1.00      | m1_subset_1(X1_52,u1_struct_0(sK5)) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_661]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1117,plain,
% 3.76/1.00      ( k2_lattices(sK5,sK7,X0_52) = k4_lattices(sK5,sK7,X0_52)
% 3.76/1.00      | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_835,c_837]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1741,plain,
% 3.76/1.00      ( k2_lattices(sK5,sK7,sK8) = k4_lattices(sK5,sK7,sK8) ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_834,c_1117]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_4648,plain,
% 3.76/1.00      ( k1_lattices(sK5,k4_lattices(sK5,sK7,sK8),k2_lattices(sK5,sK7,X0_52)) = k2_lattices(sK5,sK7,k1_lattices(sK5,sK8,X0_52))
% 3.76/1.00      | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top ),
% 3.76/1.00      inference(light_normalisation,[status(thm)],[c_4633,c_1741]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8018,plain,
% 3.76/1.00      ( k1_lattices(sK5,k4_lattices(sK5,sK7,sK8),k2_lattices(sK5,sK7,sK6)) = k2_lattices(sK5,sK7,k1_lattices(sK5,sK8,sK6)) ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_836,c_4648]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1743,plain,
% 3.76/1.00      ( k2_lattices(sK5,sK7,sK6) = k4_lattices(sK5,sK7,sK6) ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_836,c_1117]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_17,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.76/1.00      | ~ l2_lattices(X1)
% 3.76/1.00      | ~ v4_lattices(X1)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2,plain,
% 3.76/1.00      ( v4_lattices(X0)
% 3.76/1.00      | ~ l3_lattices(X0)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v10_lattices(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_275,plain,
% 3.76/1.00      ( v4_lattices(X0) | ~ l3_lattices(X0) | v2_struct_0(X0) | sK5 != X0 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_27]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_276,plain,
% 3.76/1.00      ( v4_lattices(sK5) | ~ l3_lattices(sK5) | v2_struct_0(sK5) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_275]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_75,plain,
% 3.76/1.00      ( v4_lattices(sK5)
% 3.76/1.00      | ~ l3_lattices(sK5)
% 3.76/1.00      | v2_struct_0(sK5)
% 3.76/1.00      | ~ v10_lattices(sK5) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_278,plain,
% 3.76/1.00      ( v4_lattices(sK5) ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_276,c_28,c_27,c_25,c_75]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_364,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.76/1.00      | ~ l2_lattices(X1)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0)
% 3.76/1.00      | sK5 != X1 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_278]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_365,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.76/1.00      | ~ l2_lattices(sK5)
% 3.76/1.00      | v2_struct_0(sK5)
% 3.76/1.00      | k1_lattices(sK5,X0,X1) = k3_lattices(sK5,X0,X1) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_364]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_15,plain,
% 3.76/1.00      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_46,plain,
% 3.76/1.00      ( l2_lattices(sK5) | ~ l3_lattices(sK5) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_369,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.76/1.00      | k1_lattices(sK5,X0,X1) = k3_lattices(sK5,X0,X1) ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_365,c_28,c_25,c_46]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_659,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0_52,u1_struct_0(sK5))
% 3.76/1.00      | ~ m1_subset_1(X1_52,u1_struct_0(sK5))
% 3.76/1.00      | k1_lattices(sK5,X0_52,X1_52) = k3_lattices(sK5,X0_52,X1_52) ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_369]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_839,plain,
% 3.76/1.00      ( k1_lattices(sK5,X0_52,X1_52) = k3_lattices(sK5,X0_52,X1_52)
% 3.76/1.00      | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top
% 3.76/1.00      | m1_subset_1(X1_52,u1_struct_0(sK5)) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_659]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2305,plain,
% 3.76/1.00      ( k1_lattices(sK5,sK7,X0_52) = k3_lattices(sK5,sK7,X0_52)
% 3.76/1.00      | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_835,c_839]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3122,plain,
% 3.76/1.00      ( k1_lattices(sK5,sK7,sK6) = k3_lattices(sK5,sK7,sK6) ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_836,c_2305]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_14,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.76/1.00      | ~ l3_lattices(X1)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v9_lattices(X1)
% 3.76/1.00      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2 ),
% 3.76/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_542,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.76/1.00      | ~ l3_lattices(X1)
% 3.76/1.00      | ~ v9_lattices(X1)
% 3.76/1.00      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
% 3.76/1.00      | sK5 != X1 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_28]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_543,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.76/1.00      | ~ l3_lattices(sK5)
% 3.76/1.00      | ~ v9_lattices(sK5)
% 3.76/1.00      | k2_lattices(sK5,X0,k1_lattices(sK5,X0,X1)) = X0 ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_542]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_0,plain,
% 3.76/1.00      ( ~ l3_lattices(X0)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v10_lattices(X0)
% 3.76/1.00      | v9_lattices(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_297,plain,
% 3.76/1.00      ( ~ l3_lattices(X0) | v2_struct_0(X0) | v9_lattices(X0) | sK5 != X0 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_27]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_298,plain,
% 3.76/1.00      ( ~ l3_lattices(sK5) | v2_struct_0(sK5) | v9_lattices(sK5) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_297]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_81,plain,
% 3.76/1.00      ( ~ l3_lattices(sK5)
% 3.76/1.00      | v2_struct_0(sK5)
% 3.76/1.00      | ~ v10_lattices(sK5)
% 3.76/1.00      | v9_lattices(sK5) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_300,plain,
% 3.76/1.00      ( v9_lattices(sK5) ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_298,c_28,c_27,c_25,c_81]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_486,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.76/1.00      | ~ l3_lattices(X1)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
% 3.76/1.00      | sK5 != X1 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_300]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_487,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.76/1.00      | ~ l3_lattices(sK5)
% 3.76/1.00      | v2_struct_0(sK5)
% 3.76/1.00      | k2_lattices(sK5,X0,k1_lattices(sK5,X0,X1)) = X0 ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_486]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_546,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.76/1.00      | k2_lattices(sK5,X0,k1_lattices(sK5,X0,X1)) = X0 ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_543,c_28,c_25,c_487]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_657,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0_52,u1_struct_0(sK5))
% 3.76/1.00      | ~ m1_subset_1(X1_52,u1_struct_0(sK5))
% 3.76/1.00      | k2_lattices(sK5,X0_52,k1_lattices(sK5,X0_52,X1_52)) = X0_52 ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_546]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_841,plain,
% 3.76/1.00      ( k2_lattices(sK5,X0_52,k1_lattices(sK5,X0_52,X1_52)) = X0_52
% 3.76/1.00      | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top
% 3.76/1.00      | m1_subset_1(X1_52,u1_struct_0(sK5)) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_657]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1023,plain,
% 3.76/1.00      ( k2_lattices(sK5,sK7,k1_lattices(sK5,sK7,X0_52)) = sK7
% 3.76/1.00      | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_835,c_841]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1295,plain,
% 3.76/1.00      ( k2_lattices(sK5,sK7,k1_lattices(sK5,sK7,sK6)) = sK7 ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_836,c_1023]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3349,plain,
% 3.76/1.00      ( k2_lattices(sK5,sK7,k3_lattices(sK5,sK7,sK6)) = sK7 ),
% 3.76/1.00      inference(demodulation,[status(thm)],[c_3122,c_1295]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_4,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.76/1.00      | ~ l2_lattices(X1)
% 3.76/1.00      | ~ v4_lattices(X1)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_385,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.76/1.00      | ~ l2_lattices(X1)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
% 3.76/1.00      | sK5 != X1 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_278]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_386,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.76/1.00      | ~ l2_lattices(sK5)
% 3.76/1.00      | v2_struct_0(sK5)
% 3.76/1.00      | k3_lattices(sK5,X0,X1) = k3_lattices(sK5,X1,X0) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_385]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_390,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.76/1.00      | k3_lattices(sK5,X0,X1) = k3_lattices(sK5,X1,X0) ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_386,c_28,c_25,c_46]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_658,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0_52,u1_struct_0(sK5))
% 3.76/1.00      | ~ m1_subset_1(X1_52,u1_struct_0(sK5))
% 3.76/1.00      | k3_lattices(sK5,X0_52,X1_52) = k3_lattices(sK5,X1_52,X0_52) ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_390]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_840,plain,
% 3.76/1.00      ( k3_lattices(sK5,X0_52,X1_52) = k3_lattices(sK5,X1_52,X0_52)
% 3.76/1.00      | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top
% 3.76/1.00      | m1_subset_1(X1_52,u1_struct_0(sK5)) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_658]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2960,plain,
% 3.76/1.00      ( k3_lattices(sK5,X0_52,sK7) = k3_lattices(sK5,sK7,X0_52)
% 3.76/1.00      | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_835,c_840]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_4248,plain,
% 3.76/1.00      ( k3_lattices(sK5,sK7,sK6) = k3_lattices(sK5,sK6,sK7) ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_836,c_2960]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2959,plain,
% 3.76/1.00      ( k3_lattices(sK5,X0_52,sK8) = k3_lattices(sK5,sK8,X0_52)
% 3.76/1.00      | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_834,c_840]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3704,plain,
% 3.76/1.00      ( k3_lattices(sK5,sK8,sK6) = k3_lattices(sK5,sK6,sK8) ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_836,c_2959]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_20,negated_conjecture,
% 3.76/1.00      ( k3_lattices(sK5,sK6,sK7) = k3_lattices(sK5,sK6,sK8) ),
% 3.76/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_666,negated_conjecture,
% 3.76/1.00      ( k3_lattices(sK5,sK6,sK7) = k3_lattices(sK5,sK6,sK8) ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3939,plain,
% 3.76/1.00      ( k3_lattices(sK5,sK8,sK6) = k3_lattices(sK5,sK6,sK7) ),
% 3.76/1.00      inference(demodulation,[status(thm)],[c_3704,c_666]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_4252,plain,
% 3.76/1.00      ( k3_lattices(sK5,sK7,sK6) = k3_lattices(sK5,sK8,sK6) ),
% 3.76/1.00      inference(demodulation,[status(thm)],[c_4248,c_3939]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2304,plain,
% 3.76/1.00      ( k1_lattices(sK5,sK8,X0_52) = k3_lattices(sK5,sK8,X0_52)
% 3.76/1.00      | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_834,c_839]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2836,plain,
% 3.76/1.00      ( k1_lattices(sK5,sK8,sK6) = k3_lattices(sK5,sK8,sK6) ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_836,c_2304]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_4328,plain,
% 3.76/1.00      ( k1_lattices(sK5,sK8,sK6) = k3_lattices(sK5,sK7,sK6) ),
% 3.76/1.00      inference(demodulation,[status(thm)],[c_4252,c_2836]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3910,plain,
% 3.76/1.00      ( k1_lattices(sK5,k2_lattices(sK5,sK8,X0_52),k2_lattices(sK5,sK8,X1_52)) = k2_lattices(sK5,sK8,k1_lattices(sK5,X0_52,X1_52))
% 3.76/1.00      | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top
% 3.76/1.00      | m1_subset_1(X1_52,u1_struct_0(sK5)) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_834,c_842]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_4494,plain,
% 3.76/1.00      ( k1_lattices(sK5,k2_lattices(sK5,sK8,sK7),k2_lattices(sK5,sK8,X0_52)) = k2_lattices(sK5,sK8,k1_lattices(sK5,sK7,X0_52))
% 3.76/1.00      | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_835,c_3910]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_4521,plain,
% 3.76/1.00      ( k1_lattices(sK5,k2_lattices(sK5,sK8,sK7),k2_lattices(sK5,sK8,sK6)) = k2_lattices(sK5,sK8,k1_lattices(sK5,sK7,sK6)) ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_836,c_4494]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_4523,plain,
% 3.76/1.00      ( k1_lattices(sK5,k2_lattices(sK5,sK8,sK7),k2_lattices(sK5,sK8,sK6)) = k2_lattices(sK5,sK8,k3_lattices(sK5,sK7,sK6)) ),
% 3.76/1.00      inference(light_normalisation,[status(thm)],[c_4521,c_3122]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.76/1.00      | ~ l1_lattices(X1)
% 3.76/1.00      | ~ v6_lattices(X1)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_335,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.76/1.00      | ~ l1_lattices(X1)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
% 3.76/1.00      | sK5 != X1 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_289]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_336,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.76/1.00      | ~ l1_lattices(sK5)
% 3.76/1.00      | v2_struct_0(sK5)
% 3.76/1.00      | k4_lattices(sK5,X0,X1) = k4_lattices(sK5,X1,X0) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_335]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_340,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.76/1.00      | k4_lattices(sK5,X0,X1) = k4_lattices(sK5,X1,X0) ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_336,c_28,c_25,c_43]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_660,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0_52,u1_struct_0(sK5))
% 3.76/1.00      | ~ m1_subset_1(X1_52,u1_struct_0(sK5))
% 3.76/1.00      | k4_lattices(sK5,X0_52,X1_52) = k4_lattices(sK5,X1_52,X0_52) ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_340]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_838,plain,
% 3.76/1.00      ( k4_lattices(sK5,X0_52,X1_52) = k4_lattices(sK5,X1_52,X0_52)
% 3.76/1.00      | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top
% 3.76/1.00      | m1_subset_1(X1_52,u1_struct_0(sK5)) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_660]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1592,plain,
% 3.76/1.00      ( k4_lattices(sK5,X0_52,sK8) = k4_lattices(sK5,sK8,X0_52)
% 3.76/1.00      | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_834,c_838]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2170,plain,
% 3.76/1.00      ( k4_lattices(sK5,sK7,sK8) = k4_lattices(sK5,sK8,sK7) ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_835,c_1592]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1116,plain,
% 3.76/1.00      ( k2_lattices(sK5,sK8,X0_52) = k4_lattices(sK5,sK8,X0_52)
% 3.76/1.00      | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_834,c_837]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1580,plain,
% 3.76/1.00      ( k2_lattices(sK5,sK8,sK7) = k4_lattices(sK5,sK8,sK7) ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_835,c_1116]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2327,plain,
% 3.76/1.00      ( k2_lattices(sK5,sK8,sK7) = k4_lattices(sK5,sK7,sK8) ),
% 3.76/1.00      inference(demodulation,[status(thm)],[c_2170,c_1580]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1593,plain,
% 3.76/1.00      ( k4_lattices(sK5,X0_52,sK7) = k4_lattices(sK5,sK7,X0_52)
% 3.76/1.00      | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_835,c_838]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2612,plain,
% 3.76/1.00      ( k4_lattices(sK5,sK7,sK6) = k4_lattices(sK5,sK6,sK7) ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_836,c_1593]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2171,plain,
% 3.76/1.00      ( k4_lattices(sK5,sK8,sK6) = k4_lattices(sK5,sK6,sK8) ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_836,c_1592]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_21,negated_conjecture,
% 3.76/1.00      ( k4_lattices(sK5,sK6,sK7) = k4_lattices(sK5,sK6,sK8) ),
% 3.76/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_665,negated_conjecture,
% 3.76/1.00      ( k4_lattices(sK5,sK6,sK7) = k4_lattices(sK5,sK6,sK8) ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2460,plain,
% 3.76/1.00      ( k4_lattices(sK5,sK8,sK6) = k4_lattices(sK5,sK6,sK7) ),
% 3.76/1.00      inference(demodulation,[status(thm)],[c_2171,c_665]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2616,plain,
% 3.76/1.00      ( k4_lattices(sK5,sK7,sK6) = k4_lattices(sK5,sK8,sK6) ),
% 3.76/1.00      inference(demodulation,[status(thm)],[c_2612,c_2460]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1581,plain,
% 3.76/1.00      ( k2_lattices(sK5,sK8,sK6) = k4_lattices(sK5,sK8,sK6) ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_836,c_1116]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2695,plain,
% 3.76/1.00      ( k2_lattices(sK5,sK8,sK6) = k4_lattices(sK5,sK7,sK6) ),
% 3.76/1.00      inference(demodulation,[status(thm)],[c_2616,c_1581]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1022,plain,
% 3.76/1.00      ( k2_lattices(sK5,sK8,k1_lattices(sK5,sK8,X0_52)) = sK8
% 3.76/1.00      | m1_subset_1(X0_52,u1_struct_0(sK5)) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_834,c_841]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1049,plain,
% 3.76/1.00      ( k2_lattices(sK5,sK8,k1_lattices(sK5,sK8,sK6)) = sK8 ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_836,c_1022]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3116,plain,
% 3.76/1.00      ( k2_lattices(sK5,sK8,k3_lattices(sK5,sK8,sK6)) = sK8 ),
% 3.76/1.00      inference(demodulation,[status(thm)],[c_2836,c_1049]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5564,plain,
% 3.76/1.00      ( k2_lattices(sK5,sK8,k3_lattices(sK5,sK7,sK6)) = sK8 ),
% 3.76/1.00      inference(light_normalisation,[status(thm)],[c_3116,c_4252]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_6183,plain,
% 3.76/1.00      ( k1_lattices(sK5,k4_lattices(sK5,sK7,sK8),k4_lattices(sK5,sK7,sK6)) = sK8 ),
% 3.76/1.00      inference(light_normalisation,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_4523,c_2327,c_2695,c_5564]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8020,plain,
% 3.76/1.00      ( sK8 = sK7 ),
% 3.76/1.00      inference(light_normalisation,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_8018,c_1743,c_3349,c_4328,c_6183]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_19,negated_conjecture,
% 3.76/1.00      ( sK7 != sK8 ),
% 3.76/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_667,negated_conjecture,
% 3.76/1.00      ( sK7 != sK8 ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8321,plain,
% 3.76/1.00      ( sK7 != sK7 ),
% 3.76/1.00      inference(demodulation,[status(thm)],[c_8020,c_667]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8322,plain,
% 3.76/1.00      ( $false ),
% 3.76/1.00      inference(equality_resolution_simp,[status(thm)],[c_8321]) ).
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.76/1.00  
% 3.76/1.00  ------                               Statistics
% 3.76/1.00  
% 3.76/1.00  ------ General
% 3.76/1.00  
% 3.76/1.00  abstr_ref_over_cycles:                  0
% 3.76/1.00  abstr_ref_under_cycles:                 0
% 3.76/1.00  gc_basic_clause_elim:                   0
% 3.76/1.00  forced_gc_time:                         0
% 3.76/1.00  parsing_time:                           0.009
% 3.76/1.00  unif_index_cands_time:                  0.
% 3.76/1.00  unif_index_add_time:                    0.
% 3.76/1.00  orderings_time:                         0.
% 3.76/1.00  out_proof_time:                         0.011
% 3.76/1.00  total_time:                             0.33
% 3.76/1.00  num_of_symbols:                         55
% 3.76/1.00  num_of_terms:                           10327
% 3.76/1.00  
% 3.76/1.00  ------ Preprocessing
% 3.76/1.00  
% 3.76/1.00  num_of_splits:                          0
% 3.76/1.00  num_of_split_atoms:                     0
% 3.76/1.00  num_of_reused_defs:                     0
% 3.76/1.00  num_eq_ax_congr_red:                    20
% 3.76/1.00  num_of_sem_filtered_clauses:            1
% 3.76/1.00  num_of_subtypes:                        3
% 3.76/1.00  monotx_restored_types:                  0
% 3.76/1.00  sat_num_of_epr_types:                   0
% 3.76/1.00  sat_num_of_non_cyclic_types:            0
% 3.76/1.00  sat_guarded_non_collapsed_types:        1
% 3.76/1.00  num_pure_diseq_elim:                    0
% 3.76/1.00  simp_replaced_by:                       0
% 3.76/1.00  res_preprocessed:                       79
% 3.76/1.00  prep_upred:                             0
% 3.76/1.00  prep_unflattend:                        20
% 3.76/1.00  smt_new_axioms:                         0
% 3.76/1.00  pred_elim_cands:                        1
% 3.76/1.00  pred_elim:                              9
% 3.76/1.00  pred_elim_cl:                           16
% 3.76/1.00  pred_elim_cycles:                       12
% 3.76/1.00  merged_defs:                            0
% 3.76/1.00  merged_defs_ncl:                        0
% 3.76/1.00  bin_hyper_res:                          0
% 3.76/1.00  prep_cycles:                            4
% 3.76/1.00  pred_elim_time:                         0.006
% 3.76/1.00  splitting_time:                         0.
% 3.76/1.00  sem_filter_time:                        0.
% 3.76/1.00  monotx_time:                            0.
% 3.76/1.00  subtype_inf_time:                       0.
% 3.76/1.00  
% 3.76/1.00  ------ Problem properties
% 3.76/1.00  
% 3.76/1.00  clauses:                                12
% 3.76/1.00  conjectures:                            6
% 3.76/1.00  epr:                                    1
% 3.76/1.00  horn:                                   12
% 3.76/1.00  ground:                                 6
% 3.76/1.00  unary:                                  6
% 3.76/1.00  binary:                                 0
% 3.76/1.00  lits:                                   25
% 3.76/1.00  lits_eq:                                9
% 3.76/1.00  fd_pure:                                0
% 3.76/1.00  fd_pseudo:                              0
% 3.76/1.00  fd_cond:                                0
% 3.76/1.00  fd_pseudo_cond:                         0
% 3.76/1.00  ac_symbols:                             0
% 3.76/1.00  
% 3.76/1.00  ------ Propositional Solver
% 3.76/1.00  
% 3.76/1.00  prop_solver_calls:                      32
% 3.76/1.00  prop_fast_solver_calls:                 672
% 3.76/1.00  smt_solver_calls:                       0
% 3.76/1.00  smt_fast_solver_calls:                  0
% 3.76/1.00  prop_num_of_clauses:                    3581
% 3.76/1.00  prop_preprocess_simplified:             9075
% 3.76/1.00  prop_fo_subsumed:                       20
% 3.76/1.00  prop_solver_time:                       0.
% 3.76/1.00  smt_solver_time:                        0.
% 3.76/1.00  smt_fast_solver_time:                   0.
% 3.76/1.00  prop_fast_solver_time:                  0.
% 3.76/1.00  prop_unsat_core_time:                   0.
% 3.76/1.00  
% 3.76/1.00  ------ QBF
% 3.76/1.00  
% 3.76/1.00  qbf_q_res:                              0
% 3.76/1.00  qbf_num_tautologies:                    0
% 3.76/1.00  qbf_prep_cycles:                        0
% 3.76/1.00  
% 3.76/1.00  ------ BMC1
% 3.76/1.00  
% 3.76/1.00  bmc1_current_bound:                     -1
% 3.76/1.00  bmc1_last_solved_bound:                 -1
% 3.76/1.00  bmc1_unsat_core_size:                   -1
% 3.76/1.00  bmc1_unsat_core_parents_size:           -1
% 3.76/1.00  bmc1_merge_next_fun:                    0
% 3.76/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.76/1.00  
% 3.76/1.00  ------ Instantiation
% 3.76/1.00  
% 3.76/1.00  inst_num_of_clauses:                    1622
% 3.76/1.00  inst_num_in_passive:                    937
% 3.76/1.00  inst_num_in_active:                     594
% 3.76/1.00  inst_num_in_unprocessed:                92
% 3.76/1.00  inst_num_of_loops:                      610
% 3.76/1.00  inst_num_of_learning_restarts:          0
% 3.76/1.00  inst_num_moves_active_passive:          9
% 3.76/1.00  inst_lit_activity:                      0
% 3.76/1.00  inst_lit_activity_moves:                0
% 3.76/1.00  inst_num_tautologies:                   0
% 3.76/1.00  inst_num_prop_implied:                  0
% 3.76/1.00  inst_num_existing_simplified:           0
% 3.76/1.00  inst_num_eq_res_simplified:             0
% 3.76/1.00  inst_num_child_elim:                    0
% 3.76/1.00  inst_num_of_dismatching_blockings:      768
% 3.76/1.00  inst_num_of_non_proper_insts:           2125
% 3.76/1.00  inst_num_of_duplicates:                 0
% 3.76/1.00  inst_inst_num_from_inst_to_res:         0
% 3.76/1.00  inst_dismatching_checking_time:         0.
% 3.76/1.00  
% 3.76/1.00  ------ Resolution
% 3.76/1.00  
% 3.76/1.00  res_num_of_clauses:                     0
% 3.76/1.00  res_num_in_passive:                     0
% 3.76/1.00  res_num_in_active:                      0
% 3.76/1.00  res_num_of_loops:                       83
% 3.76/1.00  res_forward_subset_subsumed:            124
% 3.76/1.00  res_backward_subset_subsumed:           2
% 3.76/1.00  res_forward_subsumed:                   0
% 3.76/1.00  res_backward_subsumed:                  0
% 3.76/1.00  res_forward_subsumption_resolution:     0
% 3.76/1.00  res_backward_subsumption_resolution:    0
% 3.76/1.00  res_clause_to_clause_subsumption:       200
% 3.76/1.00  res_orphan_elimination:                 0
% 3.76/1.00  res_tautology_del:                      173
% 3.76/1.00  res_num_eq_res_simplified:              0
% 3.76/1.00  res_num_sel_changes:                    0
% 3.76/1.00  res_moves_from_active_to_pass:          0
% 3.76/1.00  
% 3.76/1.00  ------ Superposition
% 3.76/1.00  
% 3.76/1.00  sup_time_total:                         0.
% 3.76/1.00  sup_time_generating:                    0.
% 3.76/1.00  sup_time_sim_full:                      0.
% 3.76/1.00  sup_time_sim_immed:                     0.
% 3.76/1.00  
% 3.76/1.00  sup_num_of_clauses:                     52
% 3.76/1.00  sup_num_in_active:                      40
% 3.76/1.00  sup_num_in_passive:                     12
% 3.76/1.00  sup_num_of_loops:                       120
% 3.76/1.00  sup_fw_superposition:                   99
% 3.76/1.00  sup_bw_superposition:                   0
% 3.76/1.00  sup_immediate_simplified:               29
% 3.76/1.00  sup_given_eliminated:                   1
% 3.76/1.00  comparisons_done:                       0
% 3.76/1.00  comparisons_avoided:                    0
% 3.76/1.00  
% 3.76/1.00  ------ Simplifications
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  sim_fw_subset_subsumed:                 0
% 3.76/1.00  sim_bw_subset_subsumed:                 0
% 3.76/1.00  sim_fw_subsumed:                        0
% 3.76/1.00  sim_bw_subsumed:                        0
% 3.76/1.00  sim_fw_subsumption_res:                 0
% 3.76/1.00  sim_bw_subsumption_res:                 0
% 3.76/1.00  sim_tautology_del:                      0
% 3.76/1.00  sim_eq_tautology_del:                   11
% 3.76/1.00  sim_eq_res_simp:                        0
% 3.76/1.00  sim_fw_demodulated:                     0
% 3.76/1.00  sim_bw_demodulated:                     80
% 3.76/1.00  sim_light_normalised:                   44
% 3.76/1.00  sim_joinable_taut:                      0
% 3.76/1.00  sim_joinable_simp:                      0
% 3.76/1.00  sim_ac_normalised:                      0
% 3.76/1.00  sim_smt_subsumption:                    0
% 3.76/1.00  
%------------------------------------------------------------------------------
