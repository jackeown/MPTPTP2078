%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1203+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:08 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.41s
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
