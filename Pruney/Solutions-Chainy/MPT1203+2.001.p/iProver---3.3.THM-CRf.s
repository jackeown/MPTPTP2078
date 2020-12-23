%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:14 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :  275 (8893 expanded)
%              Number of clauses        :  195 (2040 expanded)
%              Number of leaves         :   23 (3121 expanded)
%              Depth                    :   26
%              Number of atoms          : 1061 (70459 expanded)
%              Number of equality atoms :  351 (23731 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( X2 != X3
          & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
          & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sK11 != X2
        & k3_lattices(X0,X1,sK11) = k3_lattices(X0,X1,X2)
        & k4_lattices(X0,X1,sK11) = k4_lattices(X0,X1,X2)
        & m1_subset_1(sK11,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
              & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( sK10 != X3
            & k3_lattices(X0,X1,sK10) = k3_lattices(X0,X1,X3)
            & k4_lattices(X0,X1,sK10) = k4_lattices(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK10,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
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
                & k3_lattices(X0,sK9,X2) = k3_lattices(X0,sK9,X3)
                & k4_lattices(X0,sK9,X2) = k4_lattices(X0,sK9,X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK9,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
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
                  & k3_lattices(sK8,X1,X2) = k3_lattices(sK8,X1,X3)
                  & k4_lattices(sK8,X1,X2) = k4_lattices(sK8,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(sK8)) )
              & m1_subset_1(X2,u1_struct_0(sK8)) )
          & m1_subset_1(X1,u1_struct_0(sK8)) )
      & l3_lattices(sK8)
      & v11_lattices(sK8)
      & v10_lattices(sK8)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( sK10 != sK11
    & k3_lattices(sK8,sK9,sK10) = k3_lattices(sK8,sK9,sK11)
    & k4_lattices(sK8,sK9,sK10) = k4_lattices(sK8,sK9,sK11)
    & m1_subset_1(sK11,u1_struct_0(sK8))
    & m1_subset_1(sK10,u1_struct_0(sK8))
    & m1_subset_1(sK9,u1_struct_0(sK8))
    & l3_lattices(sK8)
    & v11_lattices(sK8)
    & v10_lattices(sK8)
    & ~ v2_struct_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f43,f66,f65,f64,f63])).

fof(f105,plain,(
    m1_subset_1(sK10,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f67])).

fof(f104,plain,(
    m1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f67])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,sK2(X0))) != k2_lattices(X0,X1,k1_lattices(X0,X2,sK2(X0)))
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f45,f48,f47,f46])).

fof(f76,plain,(
    ! [X6,X4,X0,X5] :
      ( k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v11_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f100,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f67])).

fof(f103,plain,(
    l3_lattices(sK8) ),
    inference(cnf_transformation,[],[f67])).

fof(f102,plain,(
    v11_lattices(sK8) ),
    inference(cnf_transformation,[],[f67])).

fof(f9,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f93,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f71,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f101,plain,(
    v10_lattices(sK8) ),
    inference(cnf_transformation,[],[f67])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f94,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f106,plain,(
    m1_subset_1(sK11,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f67])).

fof(f108,plain,(
    k3_lattices(sK8,sK9,sK10) = k3_lattices(sK8,sK9,sK11) ),
    inference(cnf_transformation,[],[f67])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
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

fof(f29,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f58,plain,(
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
    inference(rectify,[],[f57])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k1_lattices(X0,k2_lattices(X0,X1,sK7(X0)),sK7(X0)) != sK7(X0)
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK6(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),sK7(X0)) != sK7(X0)
            & m1_subset_1(sK7(X0),u1_struct_0(X0))
            & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f58,f60,f59])).

fof(f88,plain,(
    ! [X4,X0,X3] :
      ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f72,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k1_lattices(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f73,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
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

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k1_lattices(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
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

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f62,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f107,plain,(
    k4_lattices(sK8,sK9,sK10) = k4_lattices(sK8,sK9,sK11) ),
    inference(cnf_transformation,[],[f67])).

fof(f109,plain,(
    sK10 != sK11 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1598,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_1849,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1598])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1597,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_37])).

cnf(c_1850,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1597])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1458,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X1)
    | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_41])).

cnf(c_1459,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ v11_lattices(sK8)
    | ~ l3_lattices(sK8)
    | k1_lattices(sK8,k2_lattices(sK8,X2,X0),k2_lattices(sK8,X2,X1)) = k2_lattices(sK8,X2,k1_lattices(sK8,X0,X1)) ),
    inference(unflattening,[status(thm)],[c_1458])).

cnf(c_38,negated_conjecture,
    ( l3_lattices(sK8) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_39,negated_conjecture,
    ( v11_lattices(sK8) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1339,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_39])).

cnf(c_1340,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | v2_struct_0(sK8)
    | k1_lattices(sK8,k2_lattices(sK8,X2,X0),k2_lattices(sK8,X2,X1)) = k2_lattices(sK8,X2,k1_lattices(sK8,X0,X1)) ),
    inference(unflattening,[status(thm)],[c_1339])).

cnf(c_1461,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | k1_lattices(sK8,k2_lattices(sK8,X2,X0),k2_lattices(sK8,X2,X1)) = k2_lattices(sK8,X2,k1_lattices(sK8,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1459,c_41,c_38,c_1340])).

cnf(c_1462,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | k1_lattices(sK8,k2_lattices(sK8,X0,X1),k2_lattices(sK8,X0,X2)) = k2_lattices(sK8,X0,k1_lattices(sK8,X1,X2)) ),
    inference(renaming,[status(thm)],[c_1461])).

cnf(c_1586,plain,
    ( ~ m1_subset_1(X0_58,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_58,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_58,u1_struct_0(sK8))
    | k1_lattices(sK8,k2_lattices(sK8,X0_58,X1_58),k2_lattices(sK8,X0_58,X2_58)) = k2_lattices(sK8,X0_58,k1_lattices(sK8,X1_58,X2_58)) ),
    inference(subtyping,[status(esa)],[c_1462])).

cnf(c_1861,plain,
    ( k1_lattices(sK8,k2_lattices(sK8,X0_58,X1_58),k2_lattices(sK8,X0_58,X2_58)) = k2_lattices(sK8,X0_58,k1_lattices(sK8,X1_58,X2_58))
    | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_58,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_58,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1586])).

cnf(c_4949,plain,
    ( k1_lattices(sK8,k2_lattices(sK8,sK10,X0_58),k2_lattices(sK8,sK10,X1_58)) = k2_lattices(sK8,sK10,k1_lattices(sK8,X0_58,X1_58))
    | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_58,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1849,c_1861])).

cnf(c_5354,plain,
    ( k1_lattices(sK8,k2_lattices(sK8,sK10,sK9),k2_lattices(sK8,sK10,X0_58)) = k2_lattices(sK8,sK10,k1_lattices(sK8,sK9,X0_58))
    | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1850,c_4949])).

cnf(c_26,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_533,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_26,c_28])).

cnf(c_534,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_533])).

cnf(c_2,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_40,negated_conjecture,
    ( v10_lattices(sK8) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_440,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_40])).

cnf(c_441,plain,
    ( v6_lattices(sK8)
    | ~ l3_lattices(sK8)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_127,plain,
    ( v6_lattices(sK8)
    | ~ l3_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ v10_lattices(sK8) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_443,plain,
    ( v6_lattices(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_441,c_41,c_40,c_38,c_127])).

cnf(c_747,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_534,c_443])).

cnf(c_748,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | v2_struct_0(sK8)
    | k2_lattices(sK8,X0,X1) = k4_lattices(sK8,X0,X1) ),
    inference(unflattening,[status(thm)],[c_747])).

cnf(c_752,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k2_lattices(sK8,X0,X1) = k4_lattices(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_748,c_41,c_38])).

cnf(c_1591,plain,
    ( ~ m1_subset_1(X0_58,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_58,u1_struct_0(sK8))
    | k2_lattices(sK8,X0_58,X1_58) = k4_lattices(sK8,X0_58,X1_58) ),
    inference(subtyping,[status(esa)],[c_752])).

cnf(c_1856,plain,
    ( k2_lattices(sK8,X0_58,X1_58) = k4_lattices(sK8,X0_58,X1_58)
    | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_58,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1591])).

cnf(c_5486,plain,
    ( k2_lattices(sK8,sK10,X0_58) = k4_lattices(sK8,sK10,X0_58)
    | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1849,c_1856])).

cnf(c_5707,plain,
    ( k2_lattices(sK8,sK10,sK9) = k4_lattices(sK8,sK10,sK9) ),
    inference(superposition,[status(thm)],[c_1850,c_5486])).

cnf(c_6060,plain,
    ( k1_lattices(sK8,k4_lattices(sK8,sK10,sK9),k2_lattices(sK8,sK10,X0_58)) = k2_lattices(sK8,sK10,k1_lattices(sK8,sK9,X0_58))
    | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5354,c_5707])).

cnf(c_6065,plain,
    ( k1_lattices(sK8,k4_lattices(sK8,sK10,sK9),k2_lattices(sK8,sK10,sK10)) = k2_lattices(sK8,sK10,k1_lattices(sK8,sK9,sK10)) ),
    inference(superposition,[status(thm)],[c_1849,c_6060])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_4,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_418,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_40])).

cnf(c_419,plain,
    ( v4_lattices(sK8)
    | ~ l3_lattices(sK8)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_121,plain,
    ( v4_lattices(sK8)
    | ~ l3_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ v10_lattices(sK8) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_421,plain,
    ( v4_lattices(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_419,c_41,c_40,c_38,c_121])).

cnf(c_504,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_421])).

cnf(c_505,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ l2_lattices(sK8)
    | v2_struct_0(sK8)
    | k3_lattices(sK8,X0,X1) = k3_lattices(sK8,X1,X0) ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_25,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_68,plain,
    ( l2_lattices(sK8)
    | ~ l3_lattices(sK8) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_509,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k3_lattices(sK8,X0,X1) = k3_lattices(sK8,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_505,c_41,c_38,c_68])).

cnf(c_1595,plain,
    ( ~ m1_subset_1(X0_58,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_58,u1_struct_0(sK8))
    | k3_lattices(sK8,X0_58,X1_58) = k3_lattices(sK8,X1_58,X0_58) ),
    inference(subtyping,[status(esa)],[c_509])).

cnf(c_1852,plain,
    ( k3_lattices(sK8,X0_58,X1_58) = k3_lattices(sK8,X1_58,X0_58)
    | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_58,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1595])).

cnf(c_2533,plain,
    ( k3_lattices(sK8,X0_58,sK10) = k3_lattices(sK8,sK10,X0_58)
    | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1849,c_1852])).

cnf(c_3490,plain,
    ( k3_lattices(sK8,sK10,sK9) = k3_lattices(sK8,sK9,sK10) ),
    inference(superposition,[status(thm)],[c_1850,c_2533])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK11,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1599,negated_conjecture,
    ( m1_subset_1(sK11,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_1848,plain,
    ( m1_subset_1(sK11,u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1599])).

cnf(c_2532,plain,
    ( k3_lattices(sK8,X0_58,sK11) = k3_lattices(sK8,sK11,X0_58)
    | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1848,c_1852])).

cnf(c_2944,plain,
    ( k3_lattices(sK8,sK11,sK9) = k3_lattices(sK8,sK9,sK11) ),
    inference(superposition,[status(thm)],[c_1850,c_2532])).

cnf(c_33,negated_conjecture,
    ( k3_lattices(sK8,sK9,sK10) = k3_lattices(sK8,sK9,sK11) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1601,negated_conjecture,
    ( k3_lattices(sK8,sK9,sK10) = k3_lattices(sK8,sK9,sK11) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_3265,plain,
    ( k3_lattices(sK8,sK11,sK9) = k3_lattices(sK8,sK9,sK10) ),
    inference(demodulation,[status(thm)],[c_2944,c_1601])).

cnf(c_3603,plain,
    ( k3_lattices(sK8,sK10,sK9) = k3_lattices(sK8,sK11,sK9) ),
    inference(demodulation,[status(thm)],[c_3490,c_3265])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_483,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_421])).

cnf(c_484,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ l2_lattices(sK8)
    | v2_struct_0(sK8)
    | k1_lattices(sK8,X0,X1) = k3_lattices(sK8,X0,X1) ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_488,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k1_lattices(sK8,X0,X1) = k3_lattices(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_484,c_41,c_38,c_68])).

cnf(c_1596,plain,
    ( ~ m1_subset_1(X0_58,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_58,u1_struct_0(sK8))
    | k1_lattices(sK8,X0_58,X1_58) = k3_lattices(sK8,X0_58,X1_58) ),
    inference(subtyping,[status(esa)],[c_488])).

cnf(c_1851,plain,
    ( k1_lattices(sK8,X0_58,X1_58) = k3_lattices(sK8,X0_58,X1_58)
    | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_58,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1596])).

cnf(c_2029,plain,
    ( k1_lattices(sK8,sK9,X0_58) = k3_lattices(sK8,sK9,X0_58)
    | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1850,c_1851])).

cnf(c_2795,plain,
    ( k1_lattices(sK8,sK9,sK10) = k3_lattices(sK8,sK9,sK10) ),
    inference(superposition,[status(thm)],[c_1849,c_2029])).

cnf(c_3369,plain,
    ( k1_lattices(sK8,sK9,sK10) = k3_lattices(sK8,sK11,sK9) ),
    inference(demodulation,[status(thm)],[c_3265,c_2795])).

cnf(c_3605,plain,
    ( k1_lattices(sK8,sK9,sK10) = k3_lattices(sK8,sK10,sK9) ),
    inference(demodulation,[status(thm)],[c_3603,c_3369])).

cnf(c_5706,plain,
    ( k2_lattices(sK8,sK10,sK10) = k4_lattices(sK8,sK10,sK10) ),
    inference(superposition,[status(thm)],[c_1849,c_5486])).

cnf(c_6069,plain,
    ( k1_lattices(sK8,k4_lattices(sK8,sK10,sK9),k4_lattices(sK8,sK10,sK10)) = k2_lattices(sK8,sK10,k3_lattices(sK8,sK10,sK9)) ),
    inference(light_normalisation,[status(thm)],[c_6065,c_3605,c_5706])).

cnf(c_5487,plain,
    ( k2_lattices(sK8,sK9,X0_58) = k4_lattices(sK8,sK9,X0_58)
    | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1850,c_1856])).

cnf(c_5896,plain,
    ( k2_lattices(sK8,sK9,sK10) = k4_lattices(sK8,sK9,sK10) ),
    inference(superposition,[status(thm)],[c_1849,c_5487])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_581,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_26,c_7])).

cnf(c_582,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_581])).

cnf(c_705,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_582,c_443])).

cnf(c_706,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | v2_struct_0(sK8)
    | k4_lattices(sK8,X0,X1) = k4_lattices(sK8,X1,X0) ),
    inference(unflattening,[status(thm)],[c_705])).

cnf(c_710,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k4_lattices(sK8,X0,X1) = k4_lattices(sK8,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_706,c_41,c_38])).

cnf(c_1593,plain,
    ( ~ m1_subset_1(X0_58,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_58,u1_struct_0(sK8))
    | k4_lattices(sK8,X0_58,X1_58) = k4_lattices(sK8,X1_58,X0_58) ),
    inference(subtyping,[status(esa)],[c_710])).

cnf(c_1854,plain,
    ( k4_lattices(sK8,X0_58,X1_58) = k4_lattices(sK8,X1_58,X0_58)
    | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_58,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1593])).

cnf(c_3671,plain,
    ( k4_lattices(sK8,X0_58,sK10) = k4_lattices(sK8,sK10,X0_58)
    | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1849,c_1854])).

cnf(c_4141,plain,
    ( k4_lattices(sK8,sK10,sK9) = k4_lattices(sK8,sK9,sK10) ),
    inference(superposition,[status(thm)],[c_1850,c_3671])).

cnf(c_5899,plain,
    ( k2_lattices(sK8,sK9,sK10) = k4_lattices(sK8,sK10,sK9) ),
    inference(light_normalisation,[status(thm)],[c_5896,c_4141])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1439,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_41])).

cnf(c_1440,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v8_lattices(sK8)
    | ~ l3_lattices(sK8)
    | k1_lattices(sK8,k2_lattices(sK8,X0,X1),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_1439])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_451,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_40])).

cnf(c_452,plain,
    ( v8_lattices(sK8)
    | ~ l3_lattices(sK8)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_130,plain,
    ( v8_lattices(sK8)
    | ~ l3_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ v10_lattices(sK8) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_454,plain,
    ( v8_lattices(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_452,c_41,c_40,c_38,c_130])).

cnf(c_852,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_454])).

cnf(c_853,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | v2_struct_0(sK8)
    | k1_lattices(sK8,k2_lattices(sK8,X0,X1),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_852])).

cnf(c_1444,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k1_lattices(sK8,k2_lattices(sK8,X0,X1),X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1440,c_41,c_38,c_853])).

cnf(c_1590,plain,
    ( ~ m1_subset_1(X0_58,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_58,u1_struct_0(sK8))
    | k1_lattices(sK8,k2_lattices(sK8,X0_58,X1_58),X1_58) = X1_58 ),
    inference(subtyping,[status(esa)],[c_1444])).

cnf(c_1857,plain,
    ( k1_lattices(sK8,k2_lattices(sK8,X0_58,X1_58),X1_58) = X1_58
    | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_58,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1590])).

cnf(c_1972,plain,
    ( k1_lattices(sK8,k2_lattices(sK8,sK9,X0_58),X0_58) = X0_58
    | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1850,c_1857])).

cnf(c_2332,plain,
    ( k1_lattices(sK8,k2_lattices(sK8,sK9,sK10),sK10) = sK10 ),
    inference(superposition,[status(thm)],[c_1849,c_1972])).

cnf(c_7039,plain,
    ( k1_lattices(sK8,k4_lattices(sK8,sK10,sK9),sK10) = sK10 ),
    inference(demodulation,[status(thm)],[c_5899,c_2332])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | k1_lattices(X1,X0,X0) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_462,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v9_lattices(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_40])).

cnf(c_463,plain,
    ( ~ l3_lattices(sK8)
    | v2_struct_0(sK8)
    | v9_lattices(sK8) ),
    inference(unflattening,[status(thm)],[c_462])).

cnf(c_133,plain,
    ( ~ l3_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ v10_lattices(sK8)
    | v9_lattices(sK8) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_465,plain,
    ( v9_lattices(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_463,c_41,c_40,c_38,c_133])).

cnf(c_674,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X0,X0) = X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_465])).

cnf(c_675,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ v6_lattices(sK8)
    | ~ v8_lattices(sK8)
    | ~ l3_lattices(sK8)
    | v2_struct_0(sK8)
    | k1_lattices(sK8,X0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_674])).

cnf(c_679,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | k1_lattices(sK8,X0,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_675,c_41,c_40,c_38,c_127,c_130])).

cnf(c_1594,plain,
    ( ~ m1_subset_1(X0_58,u1_struct_0(sK8))
    | k1_lattices(sK8,X0_58,X0_58) = X0_58 ),
    inference(subtyping,[status(esa)],[c_679])).

cnf(c_1853,plain,
    ( k1_lattices(sK8,X0_58,X0_58) = X0_58
    | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1594])).

cnf(c_3094,plain,
    ( k1_lattices(sK8,sK10,sK10) = sK10 ),
    inference(superposition,[status(thm)],[c_1849,c_1853])).

cnf(c_13,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) != X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_31,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_626,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) = X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_465])).

cnf(c_627,plain,
    ( ~ r1_lattices(sK8,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ v8_lattices(sK8)
    | ~ l3_lattices(sK8)
    | v2_struct_0(sK8)
    | k2_lattices(sK8,X0,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_626])).

cnf(c_631,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r1_lattices(sK8,X0,X1)
    | k2_lattices(sK8,X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_627,c_41,c_40,c_38,c_130])).

cnf(c_632,plain,
    ( ~ r1_lattices(sK8,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k2_lattices(sK8,X0,X1) = X0 ),
    inference(renaming,[status(thm)],[c_631])).

cnf(c_896,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(sK8))
    | ~ m1_subset_1(X4,u1_struct_0(sK8))
    | ~ l2_lattices(X1)
    | v2_struct_0(X1)
    | X3 != X2
    | X4 != X0
    | k1_lattices(X1,X2,X0) != X0
    | k2_lattices(sK8,X3,X4) = X3
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_632])).

cnf(c_897,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ l2_lattices(sK8)
    | v2_struct_0(sK8)
    | k1_lattices(sK8,X0,X1) != X1
    | k2_lattices(sK8,X0,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_896])).

cnf(c_901,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k1_lattices(sK8,X0,X1) != X1
    | k2_lattices(sK8,X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_897,c_41,c_38,c_68])).

cnf(c_1589,plain,
    ( ~ m1_subset_1(X0_58,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_58,u1_struct_0(sK8))
    | k1_lattices(sK8,X0_58,X1_58) != X1_58
    | k2_lattices(sK8,X0_58,X1_58) = X0_58 ),
    inference(subtyping,[status(esa)],[c_901])).

cnf(c_1858,plain,
    ( k1_lattices(sK8,X0_58,X1_58) != X1_58
    | k2_lattices(sK8,X0_58,X1_58) = X0_58
    | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_58,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1589])).

cnf(c_6354,plain,
    ( k2_lattices(sK8,sK10,sK10) = sK10
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3094,c_1858])).

cnf(c_6357,plain,
    ( k4_lattices(sK8,sK10,sK10) = sK10
    | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6354,c_5706])).

cnf(c_47,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_7390,plain,
    ( k4_lattices(sK8,sK10,sK10) = sK10 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6357,c_47])).

cnf(c_4948,plain,
    ( k1_lattices(sK8,k2_lattices(sK8,sK11,X0_58),k2_lattices(sK8,sK11,X1_58)) = k2_lattices(sK8,sK11,k1_lattices(sK8,X0_58,X1_58))
    | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_58,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1848,c_1861])).

cnf(c_5113,plain,
    ( k1_lattices(sK8,k2_lattices(sK8,sK11,sK9),k2_lattices(sK8,sK11,X0_58)) = k2_lattices(sK8,sK11,k1_lattices(sK8,sK9,X0_58))
    | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1850,c_4948])).

cnf(c_5221,plain,
    ( k1_lattices(sK8,k2_lattices(sK8,sK11,sK9),k2_lattices(sK8,sK11,sK11)) = k2_lattices(sK8,sK11,k1_lattices(sK8,sK9,sK11)) ),
    inference(superposition,[status(thm)],[c_1848,c_5113])).

cnf(c_2794,plain,
    ( k1_lattices(sK8,sK9,sK11) = k3_lattices(sK8,sK9,sK11) ),
    inference(superposition,[status(thm)],[c_1848,c_2029])).

cnf(c_2797,plain,
    ( k1_lattices(sK8,sK9,sK11) = k3_lattices(sK8,sK9,sK10) ),
    inference(light_normalisation,[status(thm)],[c_2794,c_1601])).

cnf(c_3370,plain,
    ( k1_lattices(sK8,sK9,sK11) = k3_lattices(sK8,sK11,sK9) ),
    inference(demodulation,[status(thm)],[c_3265,c_2797])).

cnf(c_3604,plain,
    ( k1_lattices(sK8,sK9,sK11) = k3_lattices(sK8,sK10,sK9) ),
    inference(demodulation,[status(thm)],[c_3603,c_3370])).

cnf(c_5227,plain,
    ( k1_lattices(sK8,k2_lattices(sK8,sK11,sK9),k2_lattices(sK8,sK11,sK11)) = k2_lattices(sK8,sK11,k3_lattices(sK8,sK10,sK9)) ),
    inference(light_normalisation,[status(thm)],[c_5221,c_3604])).

cnf(c_5485,plain,
    ( k2_lattices(sK8,sK11,X0_58) = k4_lattices(sK8,sK11,X0_58)
    | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1848,c_1856])).

cnf(c_5623,plain,
    ( k2_lattices(sK8,sK11,sK9) = k4_lattices(sK8,sK11,sK9) ),
    inference(superposition,[status(thm)],[c_1850,c_5485])).

cnf(c_3670,plain,
    ( k4_lattices(sK8,sK11,X0_58) = k4_lattices(sK8,X0_58,sK11)
    | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1848,c_1854])).

cnf(c_3857,plain,
    ( k4_lattices(sK8,sK11,sK9) = k4_lattices(sK8,sK9,sK11) ),
    inference(superposition,[status(thm)],[c_1850,c_3670])).

cnf(c_34,negated_conjecture,
    ( k4_lattices(sK8,sK9,sK10) = k4_lattices(sK8,sK9,sK11) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1600,negated_conjecture,
    ( k4_lattices(sK8,sK9,sK10) = k4_lattices(sK8,sK9,sK11) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_4001,plain,
    ( k4_lattices(sK8,sK11,sK9) = k4_lattices(sK8,sK9,sK10) ),
    inference(demodulation,[status(thm)],[c_3857,c_1600])).

cnf(c_4142,plain,
    ( k4_lattices(sK8,sK10,sK9) = k4_lattices(sK8,sK11,sK9) ),
    inference(demodulation,[status(thm)],[c_4141,c_4001])).

cnf(c_5625,plain,
    ( k2_lattices(sK8,sK11,sK9) = k4_lattices(sK8,sK10,sK9) ),
    inference(light_normalisation,[status(thm)],[c_5623,c_4142])).

cnf(c_5895,plain,
    ( k2_lattices(sK8,sK9,sK11) = k4_lattices(sK8,sK9,sK11) ),
    inference(superposition,[status(thm)],[c_1848,c_5487])).

cnf(c_4234,plain,
    ( k4_lattices(sK8,sK10,sK9) = k4_lattices(sK8,sK9,sK11) ),
    inference(demodulation,[status(thm)],[c_4142,c_3857])).

cnf(c_5900,plain,
    ( k2_lattices(sK8,sK9,sK11) = k4_lattices(sK8,sK10,sK9) ),
    inference(light_normalisation,[status(thm)],[c_5895,c_4234])).

cnf(c_2331,plain,
    ( k1_lattices(sK8,k2_lattices(sK8,sK9,sK11),sK11) = sK11 ),
    inference(superposition,[status(thm)],[c_1848,c_1972])).

cnf(c_7040,plain,
    ( k1_lattices(sK8,k4_lattices(sK8,sK10,sK9),sK11) = sK11 ),
    inference(demodulation,[status(thm)],[c_5900,c_2331])).

cnf(c_3093,plain,
    ( k1_lattices(sK8,sK11,sK11) = sK11 ),
    inference(superposition,[status(thm)],[c_1848,c_1853])).

cnf(c_6346,plain,
    ( k2_lattices(sK8,sK11,sK11) = sK11
    | m1_subset_1(sK11,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3093,c_1858])).

cnf(c_5621,plain,
    ( k2_lattices(sK8,sK11,sK11) = k4_lattices(sK8,sK11,sK11) ),
    inference(superposition,[status(thm)],[c_1848,c_5485])).

cnf(c_6365,plain,
    ( k4_lattices(sK8,sK11,sK11) = sK11
    | m1_subset_1(sK11,u1_struct_0(sK8)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6346,c_5621])).

cnf(c_1604,plain,
    ( X0_58 = X0_58 ),
    theory(equality)).

cnf(c_1898,plain,
    ( sK11 = sK11 ),
    inference(instantiation,[status(thm)],[c_1604])).

cnf(c_1954,plain,
    ( ~ m1_subset_1(sK11,u1_struct_0(sK8))
    | k1_lattices(sK8,sK11,sK11) = sK11 ),
    inference(instantiation,[status(thm)],[c_1594])).

cnf(c_1910,plain,
    ( ~ m1_subset_1(X0_58,u1_struct_0(sK8))
    | ~ m1_subset_1(sK11,u1_struct_0(sK8))
    | k1_lattices(sK8,sK11,X0_58) != X0_58
    | k2_lattices(sK8,sK11,X0_58) = sK11 ),
    inference(instantiation,[status(thm)],[c_1589])).

cnf(c_2007,plain,
    ( ~ m1_subset_1(sK11,u1_struct_0(sK8))
    | k1_lattices(sK8,sK11,sK11) != sK11
    | k2_lattices(sK8,sK11,sK11) = sK11 ),
    inference(instantiation,[status(thm)],[c_1910])).

cnf(c_1605,plain,
    ( X0_58 != X1_58
    | X2_58 != X1_58
    | X2_58 = X0_58 ),
    theory(equality)).

cnf(c_1893,plain,
    ( X0_58 != X1_58
    | sK11 != X1_58
    | sK11 = X0_58 ),
    inference(instantiation,[status(thm)],[c_1605])).

cnf(c_1895,plain,
    ( X0_58 != sK11
    | sK11 = X0_58
    | sK11 != sK11 ),
    inference(instantiation,[status(thm)],[c_1893])).

cnf(c_1909,plain,
    ( k2_lattices(sK8,sK11,X0_58) != sK11
    | sK11 = k2_lattices(sK8,sK11,X0_58)
    | sK11 != sK11 ),
    inference(instantiation,[status(thm)],[c_1895])).

cnf(c_2085,plain,
    ( k2_lattices(sK8,sK11,sK11) != sK11
    | sK11 = k2_lattices(sK8,sK11,sK11)
    | sK11 != sK11 ),
    inference(instantiation,[status(thm)],[c_1909])).

cnf(c_2289,plain,
    ( ~ m1_subset_1(X0_58,u1_struct_0(sK8))
    | ~ m1_subset_1(sK11,u1_struct_0(sK8))
    | k2_lattices(sK8,X0_58,sK11) = k4_lattices(sK8,X0_58,sK11) ),
    inference(instantiation,[status(thm)],[c_1591])).

cnf(c_2955,plain,
    ( ~ m1_subset_1(sK11,u1_struct_0(sK8))
    | k2_lattices(sK8,sK11,sK11) = k4_lattices(sK8,sK11,sK11) ),
    inference(instantiation,[status(thm)],[c_2289])).

cnf(c_2505,plain,
    ( X0_58 != X1_58
    | X0_58 = k2_lattices(sK8,sK11,sK11)
    | k2_lattices(sK8,sK11,sK11) != X1_58 ),
    inference(instantiation,[status(thm)],[c_1605])).

cnf(c_2954,plain,
    ( X0_58 = k2_lattices(sK8,sK11,sK11)
    | X0_58 != k4_lattices(sK8,sK11,sK11)
    | k2_lattices(sK8,sK11,sK11) != k4_lattices(sK8,sK11,sK11) ),
    inference(instantiation,[status(thm)],[c_2505])).

cnf(c_3740,plain,
    ( k2_lattices(sK8,sK11,sK11) != k4_lattices(sK8,sK11,sK11)
    | k4_lattices(sK8,sK11,sK11) = k2_lattices(sK8,sK11,sK11)
    | k4_lattices(sK8,sK11,sK11) != k4_lattices(sK8,sK11,sK11) ),
    inference(instantiation,[status(thm)],[c_2954])).

cnf(c_2812,plain,
    ( ~ m1_subset_1(X0_58,u1_struct_0(sK8))
    | ~ m1_subset_1(sK11,u1_struct_0(sK8))
    | k4_lattices(sK8,X0_58,sK11) = k4_lattices(sK8,sK11,X0_58) ),
    inference(instantiation,[status(thm)],[c_1593])).

cnf(c_3741,plain,
    ( ~ m1_subset_1(sK11,u1_struct_0(sK8))
    | k4_lattices(sK8,sK11,sK11) = k4_lattices(sK8,sK11,sK11) ),
    inference(instantiation,[status(thm)],[c_2812])).

cnf(c_1920,plain,
    ( X0_58 != X1_58
    | X0_58 = sK11
    | sK11 != X1_58 ),
    inference(instantiation,[status(thm)],[c_1605])).

cnf(c_1936,plain,
    ( X0_58 != k2_lattices(sK8,sK11,X1_58)
    | X0_58 = sK11
    | sK11 != k2_lattices(sK8,sK11,X1_58) ),
    inference(instantiation,[status(thm)],[c_1920])).

cnf(c_2261,plain,
    ( X0_58 != k2_lattices(sK8,sK11,sK11)
    | X0_58 = sK11
    | sK11 != k2_lattices(sK8,sK11,sK11) ),
    inference(instantiation,[status(thm)],[c_1936])).

cnf(c_5831,plain,
    ( k4_lattices(sK8,sK11,sK11) != k2_lattices(sK8,sK11,sK11)
    | k4_lattices(sK8,sK11,sK11) = sK11
    | sK11 != k2_lattices(sK8,sK11,sK11) ),
    inference(instantiation,[status(thm)],[c_2261])).

cnf(c_7452,plain,
    ( k4_lattices(sK8,sK11,sK11) = sK11 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6365,c_35,c_1898,c_1954,c_2007,c_2085,c_2955,c_3740,c_3741,c_5831])).

cnf(c_7455,plain,
    ( k2_lattices(sK8,sK11,sK11) = sK11 ),
    inference(demodulation,[status(thm)],[c_7452,c_5621])).

cnf(c_5222,plain,
    ( k1_lattices(sK8,k2_lattices(sK8,sK11,sK9),k2_lattices(sK8,sK11,sK10)) = k2_lattices(sK8,sK11,k1_lattices(sK8,sK9,sK10)) ),
    inference(superposition,[status(thm)],[c_1849,c_5113])).

cnf(c_5226,plain,
    ( k1_lattices(sK8,k2_lattices(sK8,sK11,sK9),k2_lattices(sK8,sK11,sK10)) = k2_lattices(sK8,sK11,k3_lattices(sK8,sK10,sK9)) ),
    inference(light_normalisation,[status(thm)],[c_5222,c_3605])).

cnf(c_5622,plain,
    ( k2_lattices(sK8,sK11,sK10) = k4_lattices(sK8,sK11,sK10) ),
    inference(superposition,[status(thm)],[c_1849,c_5485])).

cnf(c_3856,plain,
    ( k4_lattices(sK8,sK10,sK11) = k4_lattices(sK8,sK11,sK10) ),
    inference(superposition,[status(thm)],[c_1849,c_3670])).

cnf(c_5626,plain,
    ( k2_lattices(sK8,sK11,sK10) = k4_lattices(sK8,sK10,sK11) ),
    inference(light_normalisation,[status(thm)],[c_5622,c_3856])).

cnf(c_6064,plain,
    ( k1_lattices(sK8,k4_lattices(sK8,sK10,sK9),k2_lattices(sK8,sK10,sK11)) = k2_lattices(sK8,sK10,k1_lattices(sK8,sK9,sK11)) ),
    inference(superposition,[status(thm)],[c_1848,c_6060])).

cnf(c_5705,plain,
    ( k2_lattices(sK8,sK10,sK11) = k4_lattices(sK8,sK10,sK11) ),
    inference(superposition,[status(thm)],[c_1848,c_5486])).

cnf(c_6070,plain,
    ( k1_lattices(sK8,k4_lattices(sK8,sK10,sK9),k4_lattices(sK8,sK10,sK11)) = k2_lattices(sK8,sK10,k3_lattices(sK8,sK10,sK9)) ),
    inference(light_normalisation,[status(thm)],[c_6064,c_3604,c_5705])).

cnf(c_8076,plain,
    ( k2_lattices(sK8,sK10,k3_lattices(sK8,sK10,sK9)) = k2_lattices(sK8,sK11,k3_lattices(sK8,sK10,sK9)) ),
    inference(light_normalisation,[status(thm)],[c_5226,c_5226,c_5625,c_5626,c_6070])).

cnf(c_8132,plain,
    ( k2_lattices(sK8,sK10,k3_lattices(sK8,sK10,sK9)) = sK11 ),
    inference(light_normalisation,[status(thm)],[c_5227,c_5227,c_5625,c_7040,c_7455,c_8076])).

cnf(c_8806,plain,
    ( sK11 = sK10 ),
    inference(light_normalisation,[status(thm)],[c_6069,c_6069,c_7039,c_7390,c_8132])).

cnf(c_32,negated_conjecture,
    ( sK10 != sK11 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1602,negated_conjecture,
    ( sK10 != sK11 ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_8849,plain,
    ( sK10 != sK10 ),
    inference(demodulation,[status(thm)],[c_8806,c_1602])).

cnf(c_8850,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_8849])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:06:31 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.40/0.93  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/0.93  
% 3.40/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.40/0.93  
% 3.40/0.93  ------  iProver source info
% 3.40/0.93  
% 3.40/0.93  git: date: 2020-06-30 10:37:57 +0100
% 3.40/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.40/0.93  git: non_committed_changes: false
% 3.40/0.93  git: last_make_outside_of_git: false
% 3.40/0.93  
% 3.40/0.93  ------ 
% 3.40/0.93  
% 3.40/0.93  ------ Input Options
% 3.40/0.93  
% 3.40/0.93  --out_options                           all
% 3.40/0.93  --tptp_safe_out                         true
% 3.40/0.93  --problem_path                          ""
% 3.40/0.93  --include_path                          ""
% 3.40/0.93  --clausifier                            res/vclausify_rel
% 3.40/0.93  --clausifier_options                    ""
% 3.40/0.93  --stdin                                 false
% 3.40/0.93  --stats_out                             all
% 3.40/0.93  
% 3.40/0.93  ------ General Options
% 3.40/0.93  
% 3.40/0.93  --fof                                   false
% 3.40/0.93  --time_out_real                         305.
% 3.40/0.93  --time_out_virtual                      -1.
% 3.40/0.93  --symbol_type_check                     false
% 3.40/0.93  --clausify_out                          false
% 3.40/0.93  --sig_cnt_out                           false
% 3.40/0.93  --trig_cnt_out                          false
% 3.40/0.93  --trig_cnt_out_tolerance                1.
% 3.40/0.93  --trig_cnt_out_sk_spl                   false
% 3.40/0.93  --abstr_cl_out                          false
% 3.40/0.93  
% 3.40/0.93  ------ Global Options
% 3.40/0.93  
% 3.40/0.93  --schedule                              default
% 3.40/0.93  --add_important_lit                     false
% 3.40/0.93  --prop_solver_per_cl                    1000
% 3.40/0.93  --min_unsat_core                        false
% 3.40/0.93  --soft_assumptions                      false
% 3.40/0.93  --soft_lemma_size                       3
% 3.40/0.93  --prop_impl_unit_size                   0
% 3.40/0.93  --prop_impl_unit                        []
% 3.40/0.93  --share_sel_clauses                     true
% 3.40/0.93  --reset_solvers                         false
% 3.40/0.93  --bc_imp_inh                            [conj_cone]
% 3.40/0.93  --conj_cone_tolerance                   3.
% 3.40/0.93  --extra_neg_conj                        none
% 3.40/0.93  --large_theory_mode                     true
% 3.40/0.93  --prolific_symb_bound                   200
% 3.40/0.93  --lt_threshold                          2000
% 3.40/0.93  --clause_weak_htbl                      true
% 3.40/0.93  --gc_record_bc_elim                     false
% 3.40/0.93  
% 3.40/0.93  ------ Preprocessing Options
% 3.40/0.93  
% 3.40/0.93  --preprocessing_flag                    true
% 3.40/0.93  --time_out_prep_mult                    0.1
% 3.40/0.93  --splitting_mode                        input
% 3.40/0.93  --splitting_grd                         true
% 3.40/0.93  --splitting_cvd                         false
% 3.40/0.93  --splitting_cvd_svl                     false
% 3.40/0.93  --splitting_nvd                         32
% 3.40/0.93  --sub_typing                            true
% 3.40/0.93  --prep_gs_sim                           true
% 3.40/0.93  --prep_unflatten                        true
% 3.40/0.93  --prep_res_sim                          true
% 3.40/0.93  --prep_upred                            true
% 3.40/0.93  --prep_sem_filter                       exhaustive
% 3.40/0.93  --prep_sem_filter_out                   false
% 3.40/0.93  --pred_elim                             true
% 3.40/0.93  --res_sim_input                         true
% 3.40/0.93  --eq_ax_congr_red                       true
% 3.40/0.93  --pure_diseq_elim                       true
% 3.40/0.93  --brand_transform                       false
% 3.40/0.93  --non_eq_to_eq                          false
% 3.40/0.93  --prep_def_merge                        true
% 3.40/0.93  --prep_def_merge_prop_impl              false
% 3.40/0.93  --prep_def_merge_mbd                    true
% 3.40/0.93  --prep_def_merge_tr_red                 false
% 3.40/0.93  --prep_def_merge_tr_cl                  false
% 3.40/0.93  --smt_preprocessing                     true
% 3.40/0.93  --smt_ac_axioms                         fast
% 3.40/0.93  --preprocessed_out                      false
% 3.40/0.93  --preprocessed_stats                    false
% 3.40/0.93  
% 3.40/0.93  ------ Abstraction refinement Options
% 3.40/0.93  
% 3.40/0.93  --abstr_ref                             []
% 3.40/0.93  --abstr_ref_prep                        false
% 3.40/0.93  --abstr_ref_until_sat                   false
% 3.40/0.93  --abstr_ref_sig_restrict                funpre
% 3.40/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 3.40/0.93  --abstr_ref_under                       []
% 3.40/0.93  
% 3.40/0.93  ------ SAT Options
% 3.40/0.93  
% 3.40/0.93  --sat_mode                              false
% 3.40/0.93  --sat_fm_restart_options                ""
% 3.40/0.93  --sat_gr_def                            false
% 3.40/0.93  --sat_epr_types                         true
% 3.40/0.93  --sat_non_cyclic_types                  false
% 3.40/0.93  --sat_finite_models                     false
% 3.40/0.93  --sat_fm_lemmas                         false
% 3.40/0.93  --sat_fm_prep                           false
% 3.40/0.93  --sat_fm_uc_incr                        true
% 3.40/0.93  --sat_out_model                         small
% 3.40/0.93  --sat_out_clauses                       false
% 3.40/0.93  
% 3.40/0.93  ------ QBF Options
% 3.40/0.93  
% 3.40/0.93  --qbf_mode                              false
% 3.40/0.93  --qbf_elim_univ                         false
% 3.40/0.93  --qbf_dom_inst                          none
% 3.40/0.93  --qbf_dom_pre_inst                      false
% 3.40/0.93  --qbf_sk_in                             false
% 3.40/0.93  --qbf_pred_elim                         true
% 3.40/0.93  --qbf_split                             512
% 3.40/0.93  
% 3.40/0.93  ------ BMC1 Options
% 3.40/0.93  
% 3.40/0.93  --bmc1_incremental                      false
% 3.40/0.93  --bmc1_axioms                           reachable_all
% 3.40/0.93  --bmc1_min_bound                        0
% 3.40/0.93  --bmc1_max_bound                        -1
% 3.40/0.93  --bmc1_max_bound_default                -1
% 3.40/0.93  --bmc1_symbol_reachability              true
% 3.40/0.93  --bmc1_property_lemmas                  false
% 3.40/0.93  --bmc1_k_induction                      false
% 3.40/0.93  --bmc1_non_equiv_states                 false
% 3.40/0.93  --bmc1_deadlock                         false
% 3.40/0.93  --bmc1_ucm                              false
% 3.40/0.93  --bmc1_add_unsat_core                   none
% 3.40/0.93  --bmc1_unsat_core_children              false
% 3.40/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 3.40/0.93  --bmc1_out_stat                         full
% 3.40/0.93  --bmc1_ground_init                      false
% 3.40/0.93  --bmc1_pre_inst_next_state              false
% 3.40/0.93  --bmc1_pre_inst_state                   false
% 3.40/0.93  --bmc1_pre_inst_reach_state             false
% 3.40/0.93  --bmc1_out_unsat_core                   false
% 3.40/0.93  --bmc1_aig_witness_out                  false
% 3.40/0.93  --bmc1_verbose                          false
% 3.40/0.93  --bmc1_dump_clauses_tptp                false
% 3.40/0.93  --bmc1_dump_unsat_core_tptp             false
% 3.40/0.93  --bmc1_dump_file                        -
% 3.40/0.93  --bmc1_ucm_expand_uc_limit              128
% 3.40/0.93  --bmc1_ucm_n_expand_iterations          6
% 3.40/0.93  --bmc1_ucm_extend_mode                  1
% 3.40/0.93  --bmc1_ucm_init_mode                    2
% 3.40/0.93  --bmc1_ucm_cone_mode                    none
% 3.40/0.93  --bmc1_ucm_reduced_relation_type        0
% 3.40/0.93  --bmc1_ucm_relax_model                  4
% 3.40/0.93  --bmc1_ucm_full_tr_after_sat            true
% 3.40/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 3.40/0.93  --bmc1_ucm_layered_model                none
% 3.40/0.93  --bmc1_ucm_max_lemma_size               10
% 3.40/0.93  
% 3.40/0.93  ------ AIG Options
% 3.40/0.93  
% 3.40/0.93  --aig_mode                              false
% 3.40/0.93  
% 3.40/0.93  ------ Instantiation Options
% 3.40/0.93  
% 3.40/0.93  --instantiation_flag                    true
% 3.40/0.93  --inst_sos_flag                         true
% 3.40/0.93  --inst_sos_phase                        true
% 3.40/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.40/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.40/0.93  --inst_lit_sel_side                     num_symb
% 3.40/0.93  --inst_solver_per_active                1400
% 3.40/0.93  --inst_solver_calls_frac                1.
% 3.40/0.93  --inst_passive_queue_type               priority_queues
% 3.40/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.40/0.93  --inst_passive_queues_freq              [25;2]
% 3.40/0.93  --inst_dismatching                      true
% 3.40/0.93  --inst_eager_unprocessed_to_passive     true
% 3.40/0.93  --inst_prop_sim_given                   true
% 3.40/0.93  --inst_prop_sim_new                     false
% 3.40/0.93  --inst_subs_new                         false
% 3.40/0.93  --inst_eq_res_simp                      false
% 3.40/0.93  --inst_subs_given                       false
% 3.40/0.93  --inst_orphan_elimination               true
% 3.40/0.93  --inst_learning_loop_flag               true
% 3.40/0.93  --inst_learning_start                   3000
% 3.40/0.93  --inst_learning_factor                  2
% 3.40/0.93  --inst_start_prop_sim_after_learn       3
% 3.40/0.93  --inst_sel_renew                        solver
% 3.40/0.93  --inst_lit_activity_flag                true
% 3.40/0.93  --inst_restr_to_given                   false
% 3.40/0.93  --inst_activity_threshold               500
% 3.40/0.93  --inst_out_proof                        true
% 3.40/0.93  
% 3.40/0.93  ------ Resolution Options
% 3.40/0.93  
% 3.40/0.93  --resolution_flag                       true
% 3.40/0.93  --res_lit_sel                           adaptive
% 3.40/0.93  --res_lit_sel_side                      none
% 3.40/0.93  --res_ordering                          kbo
% 3.40/0.93  --res_to_prop_solver                    active
% 3.40/0.93  --res_prop_simpl_new                    false
% 3.40/0.93  --res_prop_simpl_given                  true
% 3.40/0.93  --res_passive_queue_type                priority_queues
% 3.40/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.40/0.93  --res_passive_queues_freq               [15;5]
% 3.40/0.93  --res_forward_subs                      full
% 3.40/0.93  --res_backward_subs                     full
% 3.40/0.93  --res_forward_subs_resolution           true
% 3.40/0.93  --res_backward_subs_resolution          true
% 3.40/0.93  --res_orphan_elimination                true
% 3.40/0.93  --res_time_limit                        2.
% 3.40/0.93  --res_out_proof                         true
% 3.40/0.93  
% 3.40/0.93  ------ Superposition Options
% 3.40/0.93  
% 3.40/0.93  --superposition_flag                    true
% 3.40/0.93  --sup_passive_queue_type                priority_queues
% 3.40/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.40/0.93  --sup_passive_queues_freq               [8;1;4]
% 3.40/0.93  --demod_completeness_check              fast
% 3.40/0.93  --demod_use_ground                      true
% 3.40/0.93  --sup_to_prop_solver                    passive
% 3.40/0.93  --sup_prop_simpl_new                    true
% 3.40/0.93  --sup_prop_simpl_given                  true
% 3.40/0.93  --sup_fun_splitting                     true
% 3.40/0.93  --sup_smt_interval                      50000
% 3.40/0.93  
% 3.40/0.93  ------ Superposition Simplification Setup
% 3.40/0.93  
% 3.40/0.93  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.40/0.93  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.40/0.93  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.40/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.40/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 3.40/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.40/0.93  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.40/0.93  --sup_immed_triv                        [TrivRules]
% 3.40/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/0.93  --sup_immed_bw_main                     []
% 3.40/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.40/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 3.40/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/0.93  --sup_input_bw                          []
% 3.40/0.93  
% 3.40/0.93  ------ Combination Options
% 3.40/0.93  
% 3.40/0.93  --comb_res_mult                         3
% 3.40/0.93  --comb_sup_mult                         2
% 3.40/0.93  --comb_inst_mult                        10
% 3.40/0.93  
% 3.40/0.93  ------ Debug Options
% 3.40/0.93  
% 3.40/0.93  --dbg_backtrace                         false
% 3.40/0.93  --dbg_dump_prop_clauses                 false
% 3.40/0.93  --dbg_dump_prop_clauses_file            -
% 3.40/0.93  --dbg_out_stat                          false
% 3.40/0.93  ------ Parsing...
% 3.40/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.40/0.93  
% 3.40/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.40/0.93  
% 3.40/0.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.40/0.93  
% 3.40/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.40/0.93  ------ Proving...
% 3.40/0.93  ------ Problem Properties 
% 3.40/0.93  
% 3.40/0.93  
% 3.40/0.93  clauses                                 17
% 3.40/0.93  conjectures                             6
% 3.40/0.93  EPR                                     1
% 3.40/0.93  Horn                                    17
% 3.40/0.93  unary                                   6
% 3.40/0.93  binary                                  1
% 3.40/0.93  lits                                    42
% 3.40/0.93  lits eq                                 15
% 3.40/0.93  fd_pure                                 0
% 3.40/0.93  fd_pseudo                               0
% 3.40/0.93  fd_cond                                 0
% 3.40/0.93  fd_pseudo_cond                          0
% 3.40/0.93  AC symbols                              0
% 3.40/0.93  
% 3.40/0.93  ------ Schedule dynamic 5 is on 
% 3.40/0.93  
% 3.40/0.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.40/0.93  
% 3.40/0.93  
% 3.40/0.93  ------ 
% 3.40/0.93  Current options:
% 3.40/0.93  ------ 
% 3.40/0.93  
% 3.40/0.93  ------ Input Options
% 3.40/0.93  
% 3.40/0.93  --out_options                           all
% 3.40/0.93  --tptp_safe_out                         true
% 3.40/0.93  --problem_path                          ""
% 3.40/0.93  --include_path                          ""
% 3.40/0.93  --clausifier                            res/vclausify_rel
% 3.40/0.93  --clausifier_options                    ""
% 3.40/0.93  --stdin                                 false
% 3.40/0.93  --stats_out                             all
% 3.40/0.93  
% 3.40/0.93  ------ General Options
% 3.40/0.93  
% 3.40/0.93  --fof                                   false
% 3.40/0.93  --time_out_real                         305.
% 3.40/0.93  --time_out_virtual                      -1.
% 3.40/0.93  --symbol_type_check                     false
% 3.40/0.93  --clausify_out                          false
% 3.40/0.93  --sig_cnt_out                           false
% 3.40/0.93  --trig_cnt_out                          false
% 3.40/0.93  --trig_cnt_out_tolerance                1.
% 3.40/0.93  --trig_cnt_out_sk_spl                   false
% 3.40/0.93  --abstr_cl_out                          false
% 3.40/0.93  
% 3.40/0.93  ------ Global Options
% 3.40/0.93  
% 3.40/0.93  --schedule                              default
% 3.40/0.93  --add_important_lit                     false
% 3.40/0.93  --prop_solver_per_cl                    1000
% 3.40/0.93  --min_unsat_core                        false
% 3.40/0.93  --soft_assumptions                      false
% 3.40/0.93  --soft_lemma_size                       3
% 3.40/0.93  --prop_impl_unit_size                   0
% 3.40/0.93  --prop_impl_unit                        []
% 3.40/0.93  --share_sel_clauses                     true
% 3.40/0.93  --reset_solvers                         false
% 3.40/0.93  --bc_imp_inh                            [conj_cone]
% 3.40/0.93  --conj_cone_tolerance                   3.
% 3.40/0.93  --extra_neg_conj                        none
% 3.40/0.93  --large_theory_mode                     true
% 3.40/0.93  --prolific_symb_bound                   200
% 3.40/0.93  --lt_threshold                          2000
% 3.40/0.93  --clause_weak_htbl                      true
% 3.40/0.93  --gc_record_bc_elim                     false
% 3.40/0.93  
% 3.40/0.93  ------ Preprocessing Options
% 3.40/0.93  
% 3.40/0.93  --preprocessing_flag                    true
% 3.40/0.93  --time_out_prep_mult                    0.1
% 3.40/0.93  --splitting_mode                        input
% 3.40/0.93  --splitting_grd                         true
% 3.40/0.93  --splitting_cvd                         false
% 3.40/0.93  --splitting_cvd_svl                     false
% 3.40/0.93  --splitting_nvd                         32
% 3.40/0.93  --sub_typing                            true
% 3.40/0.93  --prep_gs_sim                           true
% 3.40/0.93  --prep_unflatten                        true
% 3.40/0.93  --prep_res_sim                          true
% 3.40/0.93  --prep_upred                            true
% 3.40/0.93  --prep_sem_filter                       exhaustive
% 3.40/0.93  --prep_sem_filter_out                   false
% 3.40/0.93  --pred_elim                             true
% 3.40/0.93  --res_sim_input                         true
% 3.40/0.93  --eq_ax_congr_red                       true
% 3.40/0.93  --pure_diseq_elim                       true
% 3.40/0.93  --brand_transform                       false
% 3.40/0.93  --non_eq_to_eq                          false
% 3.40/0.93  --prep_def_merge                        true
% 3.40/0.93  --prep_def_merge_prop_impl              false
% 3.40/0.93  --prep_def_merge_mbd                    true
% 3.40/0.93  --prep_def_merge_tr_red                 false
% 3.40/0.93  --prep_def_merge_tr_cl                  false
% 3.40/0.93  --smt_preprocessing                     true
% 3.40/0.93  --smt_ac_axioms                         fast
% 3.40/0.93  --preprocessed_out                      false
% 3.40/0.93  --preprocessed_stats                    false
% 3.40/0.93  
% 3.40/0.93  ------ Abstraction refinement Options
% 3.40/0.93  
% 3.40/0.93  --abstr_ref                             []
% 3.40/0.93  --abstr_ref_prep                        false
% 3.40/0.93  --abstr_ref_until_sat                   false
% 3.40/0.93  --abstr_ref_sig_restrict                funpre
% 3.40/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 3.40/0.93  --abstr_ref_under                       []
% 3.40/0.93  
% 3.40/0.93  ------ SAT Options
% 3.40/0.93  
% 3.40/0.93  --sat_mode                              false
% 3.40/0.93  --sat_fm_restart_options                ""
% 3.40/0.93  --sat_gr_def                            false
% 3.40/0.93  --sat_epr_types                         true
% 3.40/0.93  --sat_non_cyclic_types                  false
% 3.40/0.93  --sat_finite_models                     false
% 3.40/0.93  --sat_fm_lemmas                         false
% 3.40/0.93  --sat_fm_prep                           false
% 3.40/0.93  --sat_fm_uc_incr                        true
% 3.40/0.93  --sat_out_model                         small
% 3.40/0.93  --sat_out_clauses                       false
% 3.40/0.93  
% 3.40/0.93  ------ QBF Options
% 3.40/0.93  
% 3.40/0.93  --qbf_mode                              false
% 3.40/0.93  --qbf_elim_univ                         false
% 3.40/0.93  --qbf_dom_inst                          none
% 3.40/0.93  --qbf_dom_pre_inst                      false
% 3.40/0.93  --qbf_sk_in                             false
% 3.40/0.93  --qbf_pred_elim                         true
% 3.40/0.93  --qbf_split                             512
% 3.40/0.93  
% 3.40/0.93  ------ BMC1 Options
% 3.40/0.93  
% 3.40/0.93  --bmc1_incremental                      false
% 3.40/0.93  --bmc1_axioms                           reachable_all
% 3.40/0.93  --bmc1_min_bound                        0
% 3.40/0.93  --bmc1_max_bound                        -1
% 3.40/0.93  --bmc1_max_bound_default                -1
% 3.40/0.93  --bmc1_symbol_reachability              true
% 3.40/0.93  --bmc1_property_lemmas                  false
% 3.40/0.93  --bmc1_k_induction                      false
% 3.40/0.93  --bmc1_non_equiv_states                 false
% 3.40/0.93  --bmc1_deadlock                         false
% 3.40/0.93  --bmc1_ucm                              false
% 3.40/0.93  --bmc1_add_unsat_core                   none
% 3.40/0.93  --bmc1_unsat_core_children              false
% 3.40/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 3.40/0.93  --bmc1_out_stat                         full
% 3.40/0.93  --bmc1_ground_init                      false
% 3.40/0.93  --bmc1_pre_inst_next_state              false
% 3.40/0.93  --bmc1_pre_inst_state                   false
% 3.40/0.93  --bmc1_pre_inst_reach_state             false
% 3.40/0.93  --bmc1_out_unsat_core                   false
% 3.40/0.93  --bmc1_aig_witness_out                  false
% 3.40/0.93  --bmc1_verbose                          false
% 3.40/0.93  --bmc1_dump_clauses_tptp                false
% 3.40/0.93  --bmc1_dump_unsat_core_tptp             false
% 3.40/0.93  --bmc1_dump_file                        -
% 3.40/0.93  --bmc1_ucm_expand_uc_limit              128
% 3.40/0.93  --bmc1_ucm_n_expand_iterations          6
% 3.40/0.93  --bmc1_ucm_extend_mode                  1
% 3.40/0.93  --bmc1_ucm_init_mode                    2
% 3.40/0.93  --bmc1_ucm_cone_mode                    none
% 3.40/0.93  --bmc1_ucm_reduced_relation_type        0
% 3.40/0.93  --bmc1_ucm_relax_model                  4
% 3.40/0.93  --bmc1_ucm_full_tr_after_sat            true
% 3.40/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 3.40/0.93  --bmc1_ucm_layered_model                none
% 3.40/0.93  --bmc1_ucm_max_lemma_size               10
% 3.40/0.93  
% 3.40/0.93  ------ AIG Options
% 3.40/0.93  
% 3.40/0.93  --aig_mode                              false
% 3.40/0.93  
% 3.40/0.93  ------ Instantiation Options
% 3.40/0.93  
% 3.40/0.93  --instantiation_flag                    true
% 3.40/0.93  --inst_sos_flag                         true
% 3.40/0.93  --inst_sos_phase                        true
% 3.40/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.40/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.40/0.93  --inst_lit_sel_side                     none
% 3.40/0.93  --inst_solver_per_active                1400
% 3.40/0.93  --inst_solver_calls_frac                1.
% 3.40/0.93  --inst_passive_queue_type               priority_queues
% 3.40/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.40/0.93  --inst_passive_queues_freq              [25;2]
% 3.40/0.93  --inst_dismatching                      true
% 3.40/0.93  --inst_eager_unprocessed_to_passive     true
% 3.40/0.93  --inst_prop_sim_given                   true
% 3.40/0.93  --inst_prop_sim_new                     false
% 3.40/0.93  --inst_subs_new                         false
% 3.40/0.93  --inst_eq_res_simp                      false
% 3.40/0.93  --inst_subs_given                       false
% 3.40/0.93  --inst_orphan_elimination               true
% 3.40/0.93  --inst_learning_loop_flag               true
% 3.40/0.93  --inst_learning_start                   3000
% 3.40/0.93  --inst_learning_factor                  2
% 3.40/0.93  --inst_start_prop_sim_after_learn       3
% 3.40/0.93  --inst_sel_renew                        solver
% 3.40/0.93  --inst_lit_activity_flag                true
% 3.40/0.93  --inst_restr_to_given                   false
% 3.40/0.93  --inst_activity_threshold               500
% 3.40/0.93  --inst_out_proof                        true
% 3.40/0.93  
% 3.40/0.93  ------ Resolution Options
% 3.40/0.93  
% 3.40/0.93  --resolution_flag                       false
% 3.40/0.93  --res_lit_sel                           adaptive
% 3.40/0.93  --res_lit_sel_side                      none
% 3.40/0.93  --res_ordering                          kbo
% 3.40/0.93  --res_to_prop_solver                    active
% 3.40/0.93  --res_prop_simpl_new                    false
% 3.40/0.93  --res_prop_simpl_given                  true
% 3.40/0.93  --res_passive_queue_type                priority_queues
% 3.40/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.40/0.93  --res_passive_queues_freq               [15;5]
% 3.40/0.93  --res_forward_subs                      full
% 3.40/0.93  --res_backward_subs                     full
% 3.40/0.93  --res_forward_subs_resolution           true
% 3.40/0.93  --res_backward_subs_resolution          true
% 3.40/0.93  --res_orphan_elimination                true
% 3.40/0.93  --res_time_limit                        2.
% 3.40/0.93  --res_out_proof                         true
% 3.40/0.93  
% 3.40/0.93  ------ Superposition Options
% 3.40/0.93  
% 3.40/0.93  --superposition_flag                    true
% 3.40/0.93  --sup_passive_queue_type                priority_queues
% 3.40/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.40/0.93  --sup_passive_queues_freq               [8;1;4]
% 3.40/0.93  --demod_completeness_check              fast
% 3.40/0.93  --demod_use_ground                      true
% 3.40/0.93  --sup_to_prop_solver                    passive
% 3.40/0.93  --sup_prop_simpl_new                    true
% 3.40/0.93  --sup_prop_simpl_given                  true
% 3.40/0.93  --sup_fun_splitting                     true
% 3.40/0.93  --sup_smt_interval                      50000
% 3.40/0.93  
% 3.40/0.93  ------ Superposition Simplification Setup
% 3.40/0.93  
% 3.40/0.93  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.40/0.93  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.40/0.93  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.40/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.40/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 3.40/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.40/0.93  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.40/0.93  --sup_immed_triv                        [TrivRules]
% 3.40/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/0.93  --sup_immed_bw_main                     []
% 3.40/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.40/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 3.40/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/0.93  --sup_input_bw                          []
% 3.40/0.93  
% 3.40/0.93  ------ Combination Options
% 3.40/0.93  
% 3.40/0.93  --comb_res_mult                         3
% 3.40/0.93  --comb_sup_mult                         2
% 3.40/0.93  --comb_inst_mult                        10
% 3.40/0.93  
% 3.40/0.93  ------ Debug Options
% 3.40/0.93  
% 3.40/0.93  --dbg_backtrace                         false
% 3.40/0.93  --dbg_dump_prop_clauses                 false
% 3.40/0.93  --dbg_dump_prop_clauses_file            -
% 3.40/0.93  --dbg_out_stat                          false
% 3.40/0.93  
% 3.40/0.93  
% 3.40/0.93  
% 3.40/0.93  
% 3.40/0.93  ------ Proving...
% 3.40/0.93  
% 3.40/0.93  
% 3.40/0.93  % SZS status Theorem for theBenchmark.p
% 3.40/0.93  
% 3.40/0.93   Resolution empty clause
% 3.40/0.93  
% 3.40/0.93  % SZS output start CNFRefutation for theBenchmark.p
% 3.40/0.93  
% 3.40/0.93  fof(f14,conjecture,(
% 3.40/0.93    ! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 3.40/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.93  
% 3.40/0.93  fof(f15,negated_conjecture,(
% 3.40/0.93    ~! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 3.40/0.93    inference(negated_conjecture,[],[f14])).
% 3.40/0.93  
% 3.40/0.93  fof(f42,plain,(
% 3.40/0.93    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((X2 != X3 & (k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 3.40/0.93    inference(ennf_transformation,[],[f15])).
% 3.40/0.93  
% 3.40/0.93  fof(f43,plain,(
% 3.40/0.93    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 3.40/0.93    inference(flattening,[],[f42])).
% 3.40/0.93  
% 3.40/0.93  fof(f66,plain,(
% 3.40/0.93    ( ! [X2,X0,X1] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (sK11 != X2 & k3_lattices(X0,X1,sK11) = k3_lattices(X0,X1,X2) & k4_lattices(X0,X1,sK11) = k4_lattices(X0,X1,X2) & m1_subset_1(sK11,u1_struct_0(X0)))) )),
% 3.40/0.93    introduced(choice_axiom,[])).
% 3.40/0.93  
% 3.40/0.93  fof(f65,plain,(
% 3.40/0.93    ( ! [X0,X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (sK10 != X3 & k3_lattices(X0,X1,sK10) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,sK10) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK10,u1_struct_0(X0)))) )),
% 3.40/0.93    introduced(choice_axiom,[])).
% 3.40/0.93  
% 3.40/0.93  fof(f64,plain,(
% 3.40/0.93    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,sK9,X2) = k3_lattices(X0,sK9,X3) & k4_lattices(X0,sK9,X2) = k4_lattices(X0,sK9,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK9,u1_struct_0(X0)))) )),
% 3.40/0.93    introduced(choice_axiom,[])).
% 3.40/0.93  
% 3.40/0.93  fof(f63,plain,(
% 3.40/0.93    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(sK8,X1,X2) = k3_lattices(sK8,X1,X3) & k4_lattices(sK8,X1,X2) = k4_lattices(sK8,X1,X3) & m1_subset_1(X3,u1_struct_0(sK8))) & m1_subset_1(X2,u1_struct_0(sK8))) & m1_subset_1(X1,u1_struct_0(sK8))) & l3_lattices(sK8) & v11_lattices(sK8) & v10_lattices(sK8) & ~v2_struct_0(sK8))),
% 3.40/0.93    introduced(choice_axiom,[])).
% 3.40/0.93  
% 3.40/0.93  fof(f67,plain,(
% 3.40/0.93    (((sK10 != sK11 & k3_lattices(sK8,sK9,sK10) = k3_lattices(sK8,sK9,sK11) & k4_lattices(sK8,sK9,sK10) = k4_lattices(sK8,sK9,sK11) & m1_subset_1(sK11,u1_struct_0(sK8))) & m1_subset_1(sK10,u1_struct_0(sK8))) & m1_subset_1(sK9,u1_struct_0(sK8))) & l3_lattices(sK8) & v11_lattices(sK8) & v10_lattices(sK8) & ~v2_struct_0(sK8)),
% 3.40/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f43,f66,f65,f64,f63])).
% 3.40/0.93  
% 3.40/0.93  fof(f105,plain,(
% 3.40/0.93    m1_subset_1(sK10,u1_struct_0(sK8))),
% 3.40/0.93    inference(cnf_transformation,[],[f67])).
% 3.40/0.93  
% 3.40/0.93  fof(f104,plain,(
% 3.40/0.93    m1_subset_1(sK9,u1_struct_0(sK8))),
% 3.40/0.93    inference(cnf_transformation,[],[f67])).
% 3.40/0.93  
% 3.40/0.93  fof(f4,axiom,(
% 3.40/0.93    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v11_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3)))))))),
% 3.40/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.93  
% 3.40/0.93  fof(f23,plain,(
% 3.40/0.93    ! [X0] : ((v11_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.40/0.93    inference(ennf_transformation,[],[f4])).
% 3.40/0.93  
% 3.40/0.93  fof(f24,plain,(
% 3.40/0.93    ! [X0] : ((v11_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.40/0.93    inference(flattening,[],[f23])).
% 3.40/0.93  
% 3.40/0.93  fof(f44,plain,(
% 3.40/0.93    ! [X0] : (((v11_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (! [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.40/0.93    inference(nnf_transformation,[],[f24])).
% 3.40/0.93  
% 3.40/0.93  fof(f45,plain,(
% 3.40/0.93    ! [X0] : (((v11_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.40/0.93    inference(rectify,[],[f44])).
% 3.40/0.93  
% 3.40/0.93  fof(f48,plain,(
% 3.40/0.93    ( ! [X2,X1] : (! [X0] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) => (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,sK2(X0))) != k2_lattices(X0,X1,k1_lattices(X0,X2,sK2(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))) )),
% 3.40/0.93    introduced(choice_axiom,[])).
% 3.40/0.93  
% 3.40/0.93  fof(f47,plain,(
% 3.40/0.93    ( ! [X1] : (! [X0] : (? [X2] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,sK1(X0)),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,sK1(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK1(X0),u1_struct_0(X0))))) )),
% 3.40/0.93    introduced(choice_axiom,[])).
% 3.40/0.93  
% 3.40/0.93  fof(f46,plain,(
% 3.40/0.93    ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,sK0(X0),X2),k2_lattices(X0,sK0(X0),X3)) != k2_lattices(X0,sK0(X0),k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0))))),
% 3.40/0.93    introduced(choice_axiom,[])).
% 3.40/0.93  
% 3.40/0.93  fof(f49,plain,(
% 3.40/0.93    ! [X0] : (((v11_lattices(X0) | (((k1_lattices(X0,k2_lattices(X0,sK0(X0),sK1(X0)),k2_lattices(X0,sK0(X0),sK2(X0))) != k2_lattices(X0,sK0(X0),k1_lattices(X0,sK1(X0),sK2(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))) & m1_subset_1(sK1(X0),u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.40/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f45,f48,f47,f46])).
% 3.40/0.93  
% 3.40/0.93  fof(f76,plain,(
% 3.40/0.93    ( ! [X6,X4,X0,X5] : (k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v11_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.40/0.93    inference(cnf_transformation,[],[f49])).
% 3.40/0.93  
% 3.40/0.93  fof(f100,plain,(
% 3.40/0.93    ~v2_struct_0(sK8)),
% 3.40/0.93    inference(cnf_transformation,[],[f67])).
% 3.40/0.93  
% 3.40/0.93  fof(f103,plain,(
% 3.40/0.93    l3_lattices(sK8)),
% 3.40/0.93    inference(cnf_transformation,[],[f67])).
% 3.40/0.93  
% 3.40/0.93  fof(f102,plain,(
% 3.40/0.93    v11_lattices(sK8)),
% 3.40/0.93    inference(cnf_transformation,[],[f67])).
% 3.40/0.93  
% 3.40/0.93  fof(f9,axiom,(
% 3.40/0.93    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 3.40/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.93  
% 3.40/0.93  fof(f33,plain,(
% 3.40/0.93    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 3.40/0.93    inference(ennf_transformation,[],[f9])).
% 3.40/0.93  
% 3.40/0.93  fof(f93,plain,(
% 3.40/0.93    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 3.40/0.93    inference(cnf_transformation,[],[f33])).
% 3.40/0.93  
% 3.40/0.93  fof(f11,axiom,(
% 3.40/0.93    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 3.40/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.93  
% 3.40/0.93  fof(f36,plain,(
% 3.40/0.93    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.40/0.93    inference(ennf_transformation,[],[f11])).
% 3.40/0.93  
% 3.40/0.93  fof(f37,plain,(
% 3.40/0.93    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.40/0.93    inference(flattening,[],[f36])).
% 3.40/0.93  
% 3.40/0.93  fof(f96,plain,(
% 3.40/0.93    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.40/0.93    inference(cnf_transformation,[],[f37])).
% 3.40/0.93  
% 3.40/0.93  fof(f1,axiom,(
% 3.40/0.93    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.40/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.93  
% 3.40/0.93  fof(f16,plain,(
% 3.40/0.93    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.40/0.93    inference(pure_predicate_removal,[],[f1])).
% 3.40/0.93  
% 3.40/0.93  fof(f17,plain,(
% 3.40/0.93    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 3.40/0.93    inference(ennf_transformation,[],[f16])).
% 3.40/0.93  
% 3.40/0.93  fof(f18,plain,(
% 3.40/0.93    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 3.40/0.93    inference(flattening,[],[f17])).
% 3.40/0.93  
% 3.40/0.93  fof(f71,plain,(
% 3.40/0.93    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.40/0.93    inference(cnf_transformation,[],[f18])).
% 3.40/0.93  
% 3.40/0.93  fof(f101,plain,(
% 3.40/0.93    v10_lattices(sK8)),
% 3.40/0.93    inference(cnf_transformation,[],[f67])).
% 3.40/0.93  
% 3.40/0.93  fof(f2,axiom,(
% 3.40/0.93    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 3.40/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.93  
% 3.40/0.93  fof(f19,plain,(
% 3.40/0.93    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 3.40/0.93    inference(ennf_transformation,[],[f2])).
% 3.40/0.93  
% 3.40/0.93  fof(f20,plain,(
% 3.40/0.93    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 3.40/0.93    inference(flattening,[],[f19])).
% 3.40/0.93  
% 3.40/0.93  fof(f74,plain,(
% 3.40/0.93    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 3.40/0.93    inference(cnf_transformation,[],[f20])).
% 3.40/0.93  
% 3.40/0.93  fof(f69,plain,(
% 3.40/0.93    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.40/0.93    inference(cnf_transformation,[],[f18])).
% 3.40/0.93  
% 3.40/0.93  fof(f94,plain,(
% 3.40/0.93    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 3.40/0.93    inference(cnf_transformation,[],[f33])).
% 3.40/0.93  
% 3.40/0.93  fof(f106,plain,(
% 3.40/0.93    m1_subset_1(sK11,u1_struct_0(sK8))),
% 3.40/0.93    inference(cnf_transformation,[],[f67])).
% 3.40/0.93  
% 3.40/0.93  fof(f108,plain,(
% 3.40/0.93    k3_lattices(sK8,sK9,sK10) = k3_lattices(sK8,sK9,sK11)),
% 3.40/0.93    inference(cnf_transformation,[],[f67])).
% 3.40/0.93  
% 3.40/0.93  fof(f10,axiom,(
% 3.40/0.93    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 3.40/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.93  
% 3.40/0.93  fof(f34,plain,(
% 3.40/0.93    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 3.40/0.93    inference(ennf_transformation,[],[f10])).
% 3.40/0.93  
% 3.40/0.93  fof(f35,plain,(
% 3.40/0.93    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 3.40/0.93    inference(flattening,[],[f34])).
% 3.40/0.93  
% 3.40/0.93  fof(f95,plain,(
% 3.40/0.93    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 3.40/0.93    inference(cnf_transformation,[],[f35])).
% 3.40/0.93  
% 3.40/0.93  fof(f3,axiom,(
% 3.40/0.93    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 3.40/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.93  
% 3.40/0.93  fof(f21,plain,(
% 3.40/0.93    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.40/0.93    inference(ennf_transformation,[],[f3])).
% 3.40/0.93  
% 3.40/0.93  fof(f22,plain,(
% 3.40/0.93    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.40/0.93    inference(flattening,[],[f21])).
% 3.40/0.93  
% 3.40/0.93  fof(f75,plain,(
% 3.40/0.93    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.40/0.93    inference(cnf_transformation,[],[f22])).
% 3.40/0.93  
% 3.40/0.93  fof(f7,axiom,(
% 3.40/0.93    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 3.40/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.93  
% 3.40/0.93  fof(f29,plain,(
% 3.40/0.93    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.40/0.93    inference(ennf_transformation,[],[f7])).
% 3.40/0.93  
% 3.40/0.93  fof(f30,plain,(
% 3.40/0.93    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.40/0.93    inference(flattening,[],[f29])).
% 3.40/0.93  
% 3.40/0.93  fof(f57,plain,(
% 3.40/0.93    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.40/0.93    inference(nnf_transformation,[],[f30])).
% 3.40/0.93  
% 3.40/0.93  fof(f58,plain,(
% 3.40/0.93    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.40/0.93    inference(rectify,[],[f57])).
% 3.40/0.93  
% 3.40/0.93  fof(f60,plain,(
% 3.40/0.93    ( ! [X1] : (! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (k1_lattices(X0,k2_lattices(X0,X1,sK7(X0)),sK7(X0)) != sK7(X0) & m1_subset_1(sK7(X0),u1_struct_0(X0))))) )),
% 3.40/0.93    introduced(choice_axiom,[])).
% 3.40/0.93  
% 3.40/0.93  fof(f59,plain,(
% 3.40/0.93    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK6(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK6(X0),u1_struct_0(X0))))),
% 3.40/0.93    introduced(choice_axiom,[])).
% 3.40/0.93  
% 3.40/0.93  fof(f61,plain,(
% 3.40/0.93    ! [X0] : (((v8_lattices(X0) | ((k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),sK7(X0)) != sK7(X0) & m1_subset_1(sK7(X0),u1_struct_0(X0))) & m1_subset_1(sK6(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.40/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f58,f60,f59])).
% 3.40/0.93  
% 3.40/0.93  fof(f88,plain,(
% 3.40/0.93    ( ! [X4,X0,X3] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v8_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.40/0.93    inference(cnf_transformation,[],[f61])).
% 3.40/0.93  
% 3.40/0.93  fof(f72,plain,(
% 3.40/0.93    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.40/0.93    inference(cnf_transformation,[],[f18])).
% 3.40/0.93  
% 3.40/0.93  fof(f12,axiom,(
% 3.40/0.93    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_lattices(X0,X1,X1) = X1))),
% 3.40/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.93  
% 3.40/0.93  fof(f38,plain,(
% 3.40/0.93    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.40/0.93    inference(ennf_transformation,[],[f12])).
% 3.40/0.93  
% 3.40/0.93  fof(f39,plain,(
% 3.40/0.93    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.40/0.93    inference(flattening,[],[f38])).
% 3.40/0.93  
% 3.40/0.93  fof(f97,plain,(
% 3.40/0.93    ( ! [X0,X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.40/0.93    inference(cnf_transformation,[],[f39])).
% 3.40/0.93  
% 3.40/0.93  fof(f73,plain,(
% 3.40/0.93    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.40/0.93    inference(cnf_transformation,[],[f18])).
% 3.40/0.93  
% 3.40/0.93  fof(f5,axiom,(
% 3.40/0.93    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 3.40/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.93  
% 3.40/0.93  fof(f25,plain,(
% 3.40/0.93    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 3.40/0.93    inference(ennf_transformation,[],[f5])).
% 3.40/0.93  
% 3.40/0.93  fof(f26,plain,(
% 3.40/0.93    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 3.40/0.93    inference(flattening,[],[f25])).
% 3.40/0.93  
% 3.40/0.93  fof(f50,plain,(
% 3.40/0.93    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 3.40/0.93    inference(nnf_transformation,[],[f26])).
% 3.40/0.93  
% 3.40/0.93  fof(f82,plain,(
% 3.40/0.93    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 3.40/0.93    inference(cnf_transformation,[],[f50])).
% 3.40/0.93  
% 3.40/0.93  fof(f13,axiom,(
% 3.40/0.93    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 3.40/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.93  
% 3.40/0.93  fof(f40,plain,(
% 3.40/0.93    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 3.40/0.93    inference(ennf_transformation,[],[f13])).
% 3.40/0.93  
% 3.40/0.93  fof(f41,plain,(
% 3.40/0.93    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 3.40/0.93    inference(flattening,[],[f40])).
% 3.40/0.93  
% 3.40/0.93  fof(f62,plain,(
% 3.40/0.93    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 3.40/0.93    inference(nnf_transformation,[],[f41])).
% 3.40/0.93  
% 3.40/0.93  fof(f98,plain,(
% 3.40/0.93    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 3.40/0.93    inference(cnf_transformation,[],[f62])).
% 3.40/0.93  
% 3.40/0.93  fof(f107,plain,(
% 3.40/0.93    k4_lattices(sK8,sK9,sK10) = k4_lattices(sK8,sK9,sK11)),
% 3.40/0.93    inference(cnf_transformation,[],[f67])).
% 3.40/0.93  
% 3.40/0.93  fof(f109,plain,(
% 3.40/0.93    sK10 != sK11),
% 3.40/0.93    inference(cnf_transformation,[],[f67])).
% 3.40/0.93  
% 3.40/0.93  cnf(c_36,negated_conjecture,
% 3.40/0.93      ( m1_subset_1(sK10,u1_struct_0(sK8)) ),
% 3.40/0.93      inference(cnf_transformation,[],[f105]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1598,negated_conjecture,
% 3.40/0.93      ( m1_subset_1(sK10,u1_struct_0(sK8)) ),
% 3.40/0.93      inference(subtyping,[status(esa)],[c_36]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1849,plain,
% 3.40/0.93      ( m1_subset_1(sK10,u1_struct_0(sK8)) = iProver_top ),
% 3.40/0.93      inference(predicate_to_equality,[status(thm)],[c_1598]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_37,negated_conjecture,
% 3.40/0.93      ( m1_subset_1(sK9,u1_struct_0(sK8)) ),
% 3.40/0.93      inference(cnf_transformation,[],[f104]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1597,negated_conjecture,
% 3.40/0.93      ( m1_subset_1(sK9,u1_struct_0(sK8)) ),
% 3.40/0.93      inference(subtyping,[status(esa)],[c_37]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1850,plain,
% 3.40/0.93      ( m1_subset_1(sK9,u1_struct_0(sK8)) = iProver_top ),
% 3.40/0.93      inference(predicate_to_equality,[status(thm)],[c_1597]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_12,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/0.93      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.40/0.93      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.40/0.93      | ~ v11_lattices(X1)
% 3.40/0.93      | ~ l3_lattices(X1)
% 3.40/0.93      | v2_struct_0(X1)
% 3.40/0.93      | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0)) ),
% 3.40/0.93      inference(cnf_transformation,[],[f76]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_41,negated_conjecture,
% 3.40/0.93      ( ~ v2_struct_0(sK8) ),
% 3.40/0.93      inference(cnf_transformation,[],[f100]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1458,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/0.93      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.40/0.93      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.40/0.93      | ~ v11_lattices(X1)
% 3.40/0.93      | ~ l3_lattices(X1)
% 3.40/0.93      | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0))
% 3.40/0.93      | sK8 != X1 ),
% 3.40/0.93      inference(resolution_lifted,[status(thm)],[c_12,c_41]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1459,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 3.40/0.93      | ~ v11_lattices(sK8)
% 3.40/0.93      | ~ l3_lattices(sK8)
% 3.40/0.93      | k1_lattices(sK8,k2_lattices(sK8,X2,X0),k2_lattices(sK8,X2,X1)) = k2_lattices(sK8,X2,k1_lattices(sK8,X0,X1)) ),
% 3.40/0.93      inference(unflattening,[status(thm)],[c_1458]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_38,negated_conjecture,
% 3.40/0.93      ( l3_lattices(sK8) ),
% 3.40/0.93      inference(cnf_transformation,[],[f103]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_39,negated_conjecture,
% 3.40/0.93      ( v11_lattices(sK8) ),
% 3.40/0.93      inference(cnf_transformation,[],[f102]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1339,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/0.93      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.40/0.93      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.40/0.93      | ~ l3_lattices(X1)
% 3.40/0.93      | v2_struct_0(X1)
% 3.40/0.93      | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0))
% 3.40/0.93      | sK8 != X1 ),
% 3.40/0.93      inference(resolution_lifted,[status(thm)],[c_12,c_39]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1340,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 3.40/0.93      | ~ l3_lattices(sK8)
% 3.40/0.93      | v2_struct_0(sK8)
% 3.40/0.93      | k1_lattices(sK8,k2_lattices(sK8,X2,X0),k2_lattices(sK8,X2,X1)) = k2_lattices(sK8,X2,k1_lattices(sK8,X0,X1)) ),
% 3.40/0.93      inference(unflattening,[status(thm)],[c_1339]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1461,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 3.40/0.93      | k1_lattices(sK8,k2_lattices(sK8,X2,X0),k2_lattices(sK8,X2,X1)) = k2_lattices(sK8,X2,k1_lattices(sK8,X0,X1)) ),
% 3.40/0.93      inference(global_propositional_subsumption,
% 3.40/0.93                [status(thm)],
% 3.40/0.93                [c_1459,c_41,c_38,c_1340]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1462,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 3.40/0.93      | k1_lattices(sK8,k2_lattices(sK8,X0,X1),k2_lattices(sK8,X0,X2)) = k2_lattices(sK8,X0,k1_lattices(sK8,X1,X2)) ),
% 3.40/0.93      inference(renaming,[status(thm)],[c_1461]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1586,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0_58,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X1_58,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X2_58,u1_struct_0(sK8))
% 3.40/0.93      | k1_lattices(sK8,k2_lattices(sK8,X0_58,X1_58),k2_lattices(sK8,X0_58,X2_58)) = k2_lattices(sK8,X0_58,k1_lattices(sK8,X1_58,X2_58)) ),
% 3.40/0.93      inference(subtyping,[status(esa)],[c_1462]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1861,plain,
% 3.40/0.93      ( k1_lattices(sK8,k2_lattices(sK8,X0_58,X1_58),k2_lattices(sK8,X0_58,X2_58)) = k2_lattices(sK8,X0_58,k1_lattices(sK8,X1_58,X2_58))
% 3.40/0.93      | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top
% 3.40/0.93      | m1_subset_1(X1_58,u1_struct_0(sK8)) != iProver_top
% 3.40/0.93      | m1_subset_1(X2_58,u1_struct_0(sK8)) != iProver_top ),
% 3.40/0.93      inference(predicate_to_equality,[status(thm)],[c_1586]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_4949,plain,
% 3.40/0.93      ( k1_lattices(sK8,k2_lattices(sK8,sK10,X0_58),k2_lattices(sK8,sK10,X1_58)) = k2_lattices(sK8,sK10,k1_lattices(sK8,X0_58,X1_58))
% 3.40/0.93      | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top
% 3.40/0.93      | m1_subset_1(X1_58,u1_struct_0(sK8)) != iProver_top ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1849,c_1861]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_5354,plain,
% 3.40/0.93      ( k1_lattices(sK8,k2_lattices(sK8,sK10,sK9),k2_lattices(sK8,sK10,X0_58)) = k2_lattices(sK8,sK10,k1_lattices(sK8,sK9,X0_58))
% 3.40/0.93      | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1850,c_4949]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_26,plain,
% 3.40/0.93      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 3.40/0.93      inference(cnf_transformation,[],[f93]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_28,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/0.93      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.40/0.93      | ~ l1_lattices(X1)
% 3.40/0.93      | ~ v6_lattices(X1)
% 3.40/0.93      | v2_struct_0(X1)
% 3.40/0.93      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 3.40/0.93      inference(cnf_transformation,[],[f96]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_533,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/0.93      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.40/0.93      | ~ v6_lattices(X1)
% 3.40/0.93      | ~ l3_lattices(X3)
% 3.40/0.93      | v2_struct_0(X1)
% 3.40/0.93      | X1 != X3
% 3.40/0.93      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 3.40/0.93      inference(resolution_lifted,[status(thm)],[c_26,c_28]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_534,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/0.93      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.40/0.93      | ~ v6_lattices(X1)
% 3.40/0.93      | ~ l3_lattices(X1)
% 3.40/0.93      | v2_struct_0(X1)
% 3.40/0.93      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 3.40/0.93      inference(unflattening,[status(thm)],[c_533]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_2,plain,
% 3.40/0.93      ( v6_lattices(X0)
% 3.40/0.93      | ~ l3_lattices(X0)
% 3.40/0.93      | v2_struct_0(X0)
% 3.40/0.93      | ~ v10_lattices(X0) ),
% 3.40/0.93      inference(cnf_transformation,[],[f71]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_40,negated_conjecture,
% 3.40/0.93      ( v10_lattices(sK8) ),
% 3.40/0.93      inference(cnf_transformation,[],[f101]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_440,plain,
% 3.40/0.93      ( v6_lattices(X0) | ~ l3_lattices(X0) | v2_struct_0(X0) | sK8 != X0 ),
% 3.40/0.93      inference(resolution_lifted,[status(thm)],[c_2,c_40]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_441,plain,
% 3.40/0.93      ( v6_lattices(sK8) | ~ l3_lattices(sK8) | v2_struct_0(sK8) ),
% 3.40/0.93      inference(unflattening,[status(thm)],[c_440]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_127,plain,
% 3.40/0.93      ( v6_lattices(sK8)
% 3.40/0.93      | ~ l3_lattices(sK8)
% 3.40/0.93      | v2_struct_0(sK8)
% 3.40/0.93      | ~ v10_lattices(sK8) ),
% 3.40/0.93      inference(instantiation,[status(thm)],[c_2]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_443,plain,
% 3.40/0.93      ( v6_lattices(sK8) ),
% 3.40/0.93      inference(global_propositional_subsumption,
% 3.40/0.93                [status(thm)],
% 3.40/0.93                [c_441,c_41,c_40,c_38,c_127]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_747,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/0.93      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.40/0.93      | ~ l3_lattices(X1)
% 3.40/0.93      | v2_struct_0(X1)
% 3.40/0.93      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0)
% 3.40/0.93      | sK8 != X1 ),
% 3.40/0.93      inference(resolution_lifted,[status(thm)],[c_534,c_443]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_748,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/0.93      | ~ l3_lattices(sK8)
% 3.40/0.93      | v2_struct_0(sK8)
% 3.40/0.93      | k2_lattices(sK8,X0,X1) = k4_lattices(sK8,X0,X1) ),
% 3.40/0.93      inference(unflattening,[status(thm)],[c_747]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_752,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/0.93      | k2_lattices(sK8,X0,X1) = k4_lattices(sK8,X0,X1) ),
% 3.40/0.93      inference(global_propositional_subsumption,
% 3.40/0.93                [status(thm)],
% 3.40/0.93                [c_748,c_41,c_38]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1591,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0_58,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X1_58,u1_struct_0(sK8))
% 3.40/0.93      | k2_lattices(sK8,X0_58,X1_58) = k4_lattices(sK8,X0_58,X1_58) ),
% 3.40/0.93      inference(subtyping,[status(esa)],[c_752]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1856,plain,
% 3.40/0.93      ( k2_lattices(sK8,X0_58,X1_58) = k4_lattices(sK8,X0_58,X1_58)
% 3.40/0.93      | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top
% 3.40/0.93      | m1_subset_1(X1_58,u1_struct_0(sK8)) != iProver_top ),
% 3.40/0.93      inference(predicate_to_equality,[status(thm)],[c_1591]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_5486,plain,
% 3.40/0.93      ( k2_lattices(sK8,sK10,X0_58) = k4_lattices(sK8,sK10,X0_58)
% 3.40/0.93      | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1849,c_1856]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_5707,plain,
% 3.40/0.93      ( k2_lattices(sK8,sK10,sK9) = k4_lattices(sK8,sK10,sK9) ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1850,c_5486]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_6060,plain,
% 3.40/0.93      ( k1_lattices(sK8,k4_lattices(sK8,sK10,sK9),k2_lattices(sK8,sK10,X0_58)) = k2_lattices(sK8,sK10,k1_lattices(sK8,sK9,X0_58))
% 3.40/0.93      | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top ),
% 3.40/0.93      inference(light_normalisation,[status(thm)],[c_5354,c_5707]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_6065,plain,
% 3.40/0.93      ( k1_lattices(sK8,k4_lattices(sK8,sK10,sK9),k2_lattices(sK8,sK10,sK10)) = k2_lattices(sK8,sK10,k1_lattices(sK8,sK9,sK10)) ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1849,c_6060]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_6,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/0.93      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.40/0.93      | ~ l2_lattices(X1)
% 3.40/0.93      | ~ v4_lattices(X1)
% 3.40/0.93      | v2_struct_0(X1)
% 3.40/0.93      | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
% 3.40/0.93      inference(cnf_transformation,[],[f74]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_4,plain,
% 3.40/0.93      ( v4_lattices(X0)
% 3.40/0.93      | ~ l3_lattices(X0)
% 3.40/0.93      | v2_struct_0(X0)
% 3.40/0.93      | ~ v10_lattices(X0) ),
% 3.40/0.93      inference(cnf_transformation,[],[f69]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_418,plain,
% 3.40/0.93      ( v4_lattices(X0) | ~ l3_lattices(X0) | v2_struct_0(X0) | sK8 != X0 ),
% 3.40/0.93      inference(resolution_lifted,[status(thm)],[c_4,c_40]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_419,plain,
% 3.40/0.93      ( v4_lattices(sK8) | ~ l3_lattices(sK8) | v2_struct_0(sK8) ),
% 3.40/0.93      inference(unflattening,[status(thm)],[c_418]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_121,plain,
% 3.40/0.93      ( v4_lattices(sK8)
% 3.40/0.93      | ~ l3_lattices(sK8)
% 3.40/0.93      | v2_struct_0(sK8)
% 3.40/0.93      | ~ v10_lattices(sK8) ),
% 3.40/0.93      inference(instantiation,[status(thm)],[c_4]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_421,plain,
% 3.40/0.93      ( v4_lattices(sK8) ),
% 3.40/0.93      inference(global_propositional_subsumption,
% 3.40/0.93                [status(thm)],
% 3.40/0.93                [c_419,c_41,c_40,c_38,c_121]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_504,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/0.93      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.40/0.93      | ~ l2_lattices(X1)
% 3.40/0.93      | v2_struct_0(X1)
% 3.40/0.93      | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
% 3.40/0.93      | sK8 != X1 ),
% 3.40/0.93      inference(resolution_lifted,[status(thm)],[c_6,c_421]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_505,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/0.93      | ~ l2_lattices(sK8)
% 3.40/0.93      | v2_struct_0(sK8)
% 3.40/0.93      | k3_lattices(sK8,X0,X1) = k3_lattices(sK8,X1,X0) ),
% 3.40/0.93      inference(unflattening,[status(thm)],[c_504]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_25,plain,
% 3.40/0.93      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 3.40/0.93      inference(cnf_transformation,[],[f94]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_68,plain,
% 3.40/0.93      ( l2_lattices(sK8) | ~ l3_lattices(sK8) ),
% 3.40/0.93      inference(instantiation,[status(thm)],[c_25]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_509,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/0.93      | k3_lattices(sK8,X0,X1) = k3_lattices(sK8,X1,X0) ),
% 3.40/0.93      inference(global_propositional_subsumption,
% 3.40/0.93                [status(thm)],
% 3.40/0.93                [c_505,c_41,c_38,c_68]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1595,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0_58,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X1_58,u1_struct_0(sK8))
% 3.40/0.93      | k3_lattices(sK8,X0_58,X1_58) = k3_lattices(sK8,X1_58,X0_58) ),
% 3.40/0.93      inference(subtyping,[status(esa)],[c_509]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1852,plain,
% 3.40/0.93      ( k3_lattices(sK8,X0_58,X1_58) = k3_lattices(sK8,X1_58,X0_58)
% 3.40/0.93      | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top
% 3.40/0.93      | m1_subset_1(X1_58,u1_struct_0(sK8)) != iProver_top ),
% 3.40/0.93      inference(predicate_to_equality,[status(thm)],[c_1595]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_2533,plain,
% 3.40/0.93      ( k3_lattices(sK8,X0_58,sK10) = k3_lattices(sK8,sK10,X0_58)
% 3.40/0.93      | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1849,c_1852]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_3490,plain,
% 3.40/0.93      ( k3_lattices(sK8,sK10,sK9) = k3_lattices(sK8,sK9,sK10) ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1850,c_2533]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_35,negated_conjecture,
% 3.40/0.93      ( m1_subset_1(sK11,u1_struct_0(sK8)) ),
% 3.40/0.93      inference(cnf_transformation,[],[f106]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1599,negated_conjecture,
% 3.40/0.93      ( m1_subset_1(sK11,u1_struct_0(sK8)) ),
% 3.40/0.93      inference(subtyping,[status(esa)],[c_35]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1848,plain,
% 3.40/0.93      ( m1_subset_1(sK11,u1_struct_0(sK8)) = iProver_top ),
% 3.40/0.93      inference(predicate_to_equality,[status(thm)],[c_1599]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_2532,plain,
% 3.40/0.93      ( k3_lattices(sK8,X0_58,sK11) = k3_lattices(sK8,sK11,X0_58)
% 3.40/0.93      | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1848,c_1852]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_2944,plain,
% 3.40/0.93      ( k3_lattices(sK8,sK11,sK9) = k3_lattices(sK8,sK9,sK11) ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1850,c_2532]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_33,negated_conjecture,
% 3.40/0.93      ( k3_lattices(sK8,sK9,sK10) = k3_lattices(sK8,sK9,sK11) ),
% 3.40/0.93      inference(cnf_transformation,[],[f108]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1601,negated_conjecture,
% 3.40/0.93      ( k3_lattices(sK8,sK9,sK10) = k3_lattices(sK8,sK9,sK11) ),
% 3.40/0.93      inference(subtyping,[status(esa)],[c_33]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_3265,plain,
% 3.40/0.93      ( k3_lattices(sK8,sK11,sK9) = k3_lattices(sK8,sK9,sK10) ),
% 3.40/0.93      inference(demodulation,[status(thm)],[c_2944,c_1601]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_3603,plain,
% 3.40/0.93      ( k3_lattices(sK8,sK10,sK9) = k3_lattices(sK8,sK11,sK9) ),
% 3.40/0.93      inference(demodulation,[status(thm)],[c_3490,c_3265]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_27,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/0.93      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.40/0.93      | ~ l2_lattices(X1)
% 3.40/0.93      | ~ v4_lattices(X1)
% 3.40/0.93      | v2_struct_0(X1)
% 3.40/0.93      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
% 3.40/0.93      inference(cnf_transformation,[],[f95]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_483,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/0.93      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.40/0.93      | ~ l2_lattices(X1)
% 3.40/0.93      | v2_struct_0(X1)
% 3.40/0.93      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0)
% 3.40/0.93      | sK8 != X1 ),
% 3.40/0.93      inference(resolution_lifted,[status(thm)],[c_27,c_421]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_484,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/0.93      | ~ l2_lattices(sK8)
% 3.40/0.93      | v2_struct_0(sK8)
% 3.40/0.93      | k1_lattices(sK8,X0,X1) = k3_lattices(sK8,X0,X1) ),
% 3.40/0.93      inference(unflattening,[status(thm)],[c_483]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_488,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/0.93      | k1_lattices(sK8,X0,X1) = k3_lattices(sK8,X0,X1) ),
% 3.40/0.93      inference(global_propositional_subsumption,
% 3.40/0.93                [status(thm)],
% 3.40/0.93                [c_484,c_41,c_38,c_68]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1596,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0_58,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X1_58,u1_struct_0(sK8))
% 3.40/0.93      | k1_lattices(sK8,X0_58,X1_58) = k3_lattices(sK8,X0_58,X1_58) ),
% 3.40/0.93      inference(subtyping,[status(esa)],[c_488]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1851,plain,
% 3.40/0.93      ( k1_lattices(sK8,X0_58,X1_58) = k3_lattices(sK8,X0_58,X1_58)
% 3.40/0.93      | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top
% 3.40/0.93      | m1_subset_1(X1_58,u1_struct_0(sK8)) != iProver_top ),
% 3.40/0.93      inference(predicate_to_equality,[status(thm)],[c_1596]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_2029,plain,
% 3.40/0.93      ( k1_lattices(sK8,sK9,X0_58) = k3_lattices(sK8,sK9,X0_58)
% 3.40/0.93      | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1850,c_1851]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_2795,plain,
% 3.40/0.93      ( k1_lattices(sK8,sK9,sK10) = k3_lattices(sK8,sK9,sK10) ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1849,c_2029]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_3369,plain,
% 3.40/0.93      ( k1_lattices(sK8,sK9,sK10) = k3_lattices(sK8,sK11,sK9) ),
% 3.40/0.93      inference(demodulation,[status(thm)],[c_3265,c_2795]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_3605,plain,
% 3.40/0.93      ( k1_lattices(sK8,sK9,sK10) = k3_lattices(sK8,sK10,sK9) ),
% 3.40/0.93      inference(demodulation,[status(thm)],[c_3603,c_3369]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_5706,plain,
% 3.40/0.93      ( k2_lattices(sK8,sK10,sK10) = k4_lattices(sK8,sK10,sK10) ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1849,c_5486]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_6069,plain,
% 3.40/0.93      ( k1_lattices(sK8,k4_lattices(sK8,sK10,sK9),k4_lattices(sK8,sK10,sK10)) = k2_lattices(sK8,sK10,k3_lattices(sK8,sK10,sK9)) ),
% 3.40/0.93      inference(light_normalisation,[status(thm)],[c_6065,c_3605,c_5706]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_5487,plain,
% 3.40/0.93      ( k2_lattices(sK8,sK9,X0_58) = k4_lattices(sK8,sK9,X0_58)
% 3.40/0.93      | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1850,c_1856]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_5896,plain,
% 3.40/0.93      ( k2_lattices(sK8,sK9,sK10) = k4_lattices(sK8,sK9,sK10) ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1849,c_5487]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_7,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/0.93      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.40/0.93      | ~ l1_lattices(X1)
% 3.40/0.93      | ~ v6_lattices(X1)
% 3.40/0.93      | v2_struct_0(X1)
% 3.40/0.93      | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
% 3.40/0.93      inference(cnf_transformation,[],[f75]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_581,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/0.93      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.40/0.93      | ~ v6_lattices(X1)
% 3.40/0.93      | ~ l3_lattices(X3)
% 3.40/0.93      | v2_struct_0(X1)
% 3.40/0.93      | X1 != X3
% 3.40/0.93      | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
% 3.40/0.93      inference(resolution_lifted,[status(thm)],[c_26,c_7]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_582,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/0.93      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.40/0.93      | ~ v6_lattices(X1)
% 3.40/0.93      | ~ l3_lattices(X1)
% 3.40/0.93      | v2_struct_0(X1)
% 3.40/0.93      | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
% 3.40/0.93      inference(unflattening,[status(thm)],[c_581]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_705,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/0.93      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.40/0.93      | ~ l3_lattices(X1)
% 3.40/0.93      | v2_struct_0(X1)
% 3.40/0.93      | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
% 3.40/0.93      | sK8 != X1 ),
% 3.40/0.93      inference(resolution_lifted,[status(thm)],[c_582,c_443]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_706,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/0.93      | ~ l3_lattices(sK8)
% 3.40/0.93      | v2_struct_0(sK8)
% 3.40/0.93      | k4_lattices(sK8,X0,X1) = k4_lattices(sK8,X1,X0) ),
% 3.40/0.93      inference(unflattening,[status(thm)],[c_705]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_710,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/0.93      | k4_lattices(sK8,X0,X1) = k4_lattices(sK8,X1,X0) ),
% 3.40/0.93      inference(global_propositional_subsumption,
% 3.40/0.93                [status(thm)],
% 3.40/0.93                [c_706,c_41,c_38]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1593,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0_58,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X1_58,u1_struct_0(sK8))
% 3.40/0.93      | k4_lattices(sK8,X0_58,X1_58) = k4_lattices(sK8,X1_58,X0_58) ),
% 3.40/0.93      inference(subtyping,[status(esa)],[c_710]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1854,plain,
% 3.40/0.93      ( k4_lattices(sK8,X0_58,X1_58) = k4_lattices(sK8,X1_58,X0_58)
% 3.40/0.93      | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top
% 3.40/0.93      | m1_subset_1(X1_58,u1_struct_0(sK8)) != iProver_top ),
% 3.40/0.93      inference(predicate_to_equality,[status(thm)],[c_1593]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_3671,plain,
% 3.40/0.93      ( k4_lattices(sK8,X0_58,sK10) = k4_lattices(sK8,sK10,X0_58)
% 3.40/0.93      | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1849,c_1854]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_4141,plain,
% 3.40/0.93      ( k4_lattices(sK8,sK10,sK9) = k4_lattices(sK8,sK9,sK10) ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1850,c_3671]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_5899,plain,
% 3.40/0.93      ( k2_lattices(sK8,sK9,sK10) = k4_lattices(sK8,sK10,sK9) ),
% 3.40/0.93      inference(light_normalisation,[status(thm)],[c_5896,c_4141]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_23,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/0.93      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.40/0.93      | ~ v8_lattices(X1)
% 3.40/0.93      | ~ l3_lattices(X1)
% 3.40/0.93      | v2_struct_0(X1)
% 3.40/0.93      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 ),
% 3.40/0.93      inference(cnf_transformation,[],[f88]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1439,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/0.93      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.40/0.93      | ~ v8_lattices(X1)
% 3.40/0.93      | ~ l3_lattices(X1)
% 3.40/0.93      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
% 3.40/0.93      | sK8 != X1 ),
% 3.40/0.93      inference(resolution_lifted,[status(thm)],[c_23,c_41]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1440,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/0.93      | ~ v8_lattices(sK8)
% 3.40/0.93      | ~ l3_lattices(sK8)
% 3.40/0.93      | k1_lattices(sK8,k2_lattices(sK8,X0,X1),X1) = X1 ),
% 3.40/0.93      inference(unflattening,[status(thm)],[c_1439]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1,plain,
% 3.40/0.93      ( v8_lattices(X0)
% 3.40/0.93      | ~ l3_lattices(X0)
% 3.40/0.93      | v2_struct_0(X0)
% 3.40/0.93      | ~ v10_lattices(X0) ),
% 3.40/0.93      inference(cnf_transformation,[],[f72]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_451,plain,
% 3.40/0.93      ( v8_lattices(X0) | ~ l3_lattices(X0) | v2_struct_0(X0) | sK8 != X0 ),
% 3.40/0.93      inference(resolution_lifted,[status(thm)],[c_1,c_40]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_452,plain,
% 3.40/0.93      ( v8_lattices(sK8) | ~ l3_lattices(sK8) | v2_struct_0(sK8) ),
% 3.40/0.93      inference(unflattening,[status(thm)],[c_451]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_130,plain,
% 3.40/0.93      ( v8_lattices(sK8)
% 3.40/0.93      | ~ l3_lattices(sK8)
% 3.40/0.93      | v2_struct_0(sK8)
% 3.40/0.93      | ~ v10_lattices(sK8) ),
% 3.40/0.93      inference(instantiation,[status(thm)],[c_1]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_454,plain,
% 3.40/0.93      ( v8_lattices(sK8) ),
% 3.40/0.93      inference(global_propositional_subsumption,
% 3.40/0.93                [status(thm)],
% 3.40/0.93                [c_452,c_41,c_40,c_38,c_130]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_852,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/0.93      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.40/0.93      | ~ l3_lattices(X1)
% 3.40/0.93      | v2_struct_0(X1)
% 3.40/0.93      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
% 3.40/0.93      | sK8 != X1 ),
% 3.40/0.93      inference(resolution_lifted,[status(thm)],[c_23,c_454]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_853,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/0.93      | ~ l3_lattices(sK8)
% 3.40/0.93      | v2_struct_0(sK8)
% 3.40/0.93      | k1_lattices(sK8,k2_lattices(sK8,X0,X1),X1) = X1 ),
% 3.40/0.93      inference(unflattening,[status(thm)],[c_852]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1444,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/0.93      | k1_lattices(sK8,k2_lattices(sK8,X0,X1),X1) = X1 ),
% 3.40/0.93      inference(global_propositional_subsumption,
% 3.40/0.93                [status(thm)],
% 3.40/0.93                [c_1440,c_41,c_38,c_853]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1590,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0_58,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X1_58,u1_struct_0(sK8))
% 3.40/0.93      | k1_lattices(sK8,k2_lattices(sK8,X0_58,X1_58),X1_58) = X1_58 ),
% 3.40/0.93      inference(subtyping,[status(esa)],[c_1444]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1857,plain,
% 3.40/0.93      ( k1_lattices(sK8,k2_lattices(sK8,X0_58,X1_58),X1_58) = X1_58
% 3.40/0.93      | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top
% 3.40/0.93      | m1_subset_1(X1_58,u1_struct_0(sK8)) != iProver_top ),
% 3.40/0.93      inference(predicate_to_equality,[status(thm)],[c_1590]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1972,plain,
% 3.40/0.93      ( k1_lattices(sK8,k2_lattices(sK8,sK9,X0_58),X0_58) = X0_58
% 3.40/0.93      | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1850,c_1857]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_2332,plain,
% 3.40/0.93      ( k1_lattices(sK8,k2_lattices(sK8,sK9,sK10),sK10) = sK10 ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1849,c_1972]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_7039,plain,
% 3.40/0.93      ( k1_lattices(sK8,k4_lattices(sK8,sK10,sK9),sK10) = sK10 ),
% 3.40/0.93      inference(demodulation,[status(thm)],[c_5899,c_2332]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_29,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/0.93      | ~ v6_lattices(X1)
% 3.40/0.93      | ~ v8_lattices(X1)
% 3.40/0.93      | ~ l3_lattices(X1)
% 3.40/0.93      | v2_struct_0(X1)
% 3.40/0.93      | ~ v9_lattices(X1)
% 3.40/0.93      | k1_lattices(X1,X0,X0) = X0 ),
% 3.40/0.93      inference(cnf_transformation,[],[f97]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_0,plain,
% 3.40/0.93      ( ~ l3_lattices(X0)
% 3.40/0.93      | v2_struct_0(X0)
% 3.40/0.93      | ~ v10_lattices(X0)
% 3.40/0.93      | v9_lattices(X0) ),
% 3.40/0.93      inference(cnf_transformation,[],[f73]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_462,plain,
% 3.40/0.93      ( ~ l3_lattices(X0) | v2_struct_0(X0) | v9_lattices(X0) | sK8 != X0 ),
% 3.40/0.93      inference(resolution_lifted,[status(thm)],[c_0,c_40]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_463,plain,
% 3.40/0.93      ( ~ l3_lattices(sK8) | v2_struct_0(sK8) | v9_lattices(sK8) ),
% 3.40/0.93      inference(unflattening,[status(thm)],[c_462]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_133,plain,
% 3.40/0.93      ( ~ l3_lattices(sK8)
% 3.40/0.93      | v2_struct_0(sK8)
% 3.40/0.93      | ~ v10_lattices(sK8)
% 3.40/0.93      | v9_lattices(sK8) ),
% 3.40/0.93      inference(instantiation,[status(thm)],[c_0]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_465,plain,
% 3.40/0.93      ( v9_lattices(sK8) ),
% 3.40/0.93      inference(global_propositional_subsumption,
% 3.40/0.93                [status(thm)],
% 3.40/0.93                [c_463,c_41,c_40,c_38,c_133]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_674,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/0.93      | ~ v6_lattices(X1)
% 3.40/0.93      | ~ v8_lattices(X1)
% 3.40/0.93      | ~ l3_lattices(X1)
% 3.40/0.93      | v2_struct_0(X1)
% 3.40/0.93      | k1_lattices(X1,X0,X0) = X0
% 3.40/0.93      | sK8 != X1 ),
% 3.40/0.93      inference(resolution_lifted,[status(thm)],[c_29,c_465]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_675,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/0.93      | ~ v6_lattices(sK8)
% 3.40/0.93      | ~ v8_lattices(sK8)
% 3.40/0.93      | ~ l3_lattices(sK8)
% 3.40/0.93      | v2_struct_0(sK8)
% 3.40/0.93      | k1_lattices(sK8,X0,X0) = X0 ),
% 3.40/0.93      inference(unflattening,[status(thm)],[c_674]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_679,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(sK8)) | k1_lattices(sK8,X0,X0) = X0 ),
% 3.40/0.93      inference(global_propositional_subsumption,
% 3.40/0.93                [status(thm)],
% 3.40/0.93                [c_675,c_41,c_40,c_38,c_127,c_130]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1594,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0_58,u1_struct_0(sK8))
% 3.40/0.93      | k1_lattices(sK8,X0_58,X0_58) = X0_58 ),
% 3.40/0.93      inference(subtyping,[status(esa)],[c_679]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1853,plain,
% 3.40/0.93      ( k1_lattices(sK8,X0_58,X0_58) = X0_58
% 3.40/0.93      | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top ),
% 3.40/0.93      inference(predicate_to_equality,[status(thm)],[c_1594]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_3094,plain,
% 3.40/0.93      ( k1_lattices(sK8,sK10,sK10) = sK10 ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1849,c_1853]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_13,plain,
% 3.40/0.93      ( r1_lattices(X0,X1,X2)
% 3.40/0.93      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.40/0.93      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/0.93      | ~ l2_lattices(X0)
% 3.40/0.93      | v2_struct_0(X0)
% 3.40/0.93      | k1_lattices(X0,X1,X2) != X2 ),
% 3.40/0.93      inference(cnf_transformation,[],[f82]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_31,plain,
% 3.40/0.93      ( ~ r1_lattices(X0,X1,X2)
% 3.40/0.93      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.40/0.93      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/0.93      | ~ v8_lattices(X0)
% 3.40/0.93      | ~ l3_lattices(X0)
% 3.40/0.93      | v2_struct_0(X0)
% 3.40/0.93      | ~ v9_lattices(X0)
% 3.40/0.93      | k2_lattices(X0,X1,X2) = X1 ),
% 3.40/0.93      inference(cnf_transformation,[],[f98]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_626,plain,
% 3.40/0.93      ( ~ r1_lattices(X0,X1,X2)
% 3.40/0.93      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.40/0.93      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/0.93      | ~ v8_lattices(X0)
% 3.40/0.93      | ~ l3_lattices(X0)
% 3.40/0.93      | v2_struct_0(X0)
% 3.40/0.93      | k2_lattices(X0,X1,X2) = X1
% 3.40/0.93      | sK8 != X0 ),
% 3.40/0.93      inference(resolution_lifted,[status(thm)],[c_31,c_465]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_627,plain,
% 3.40/0.93      ( ~ r1_lattices(sK8,X0,X1)
% 3.40/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/0.93      | ~ v8_lattices(sK8)
% 3.40/0.93      | ~ l3_lattices(sK8)
% 3.40/0.93      | v2_struct_0(sK8)
% 3.40/0.93      | k2_lattices(sK8,X0,X1) = X0 ),
% 3.40/0.93      inference(unflattening,[status(thm)],[c_626]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_631,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/0.93      | ~ r1_lattices(sK8,X0,X1)
% 3.40/0.93      | k2_lattices(sK8,X0,X1) = X0 ),
% 3.40/0.93      inference(global_propositional_subsumption,
% 3.40/0.93                [status(thm)],
% 3.40/0.93                [c_627,c_41,c_40,c_38,c_130]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_632,plain,
% 3.40/0.93      ( ~ r1_lattices(sK8,X0,X1)
% 3.40/0.93      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/0.93      | k2_lattices(sK8,X0,X1) = X0 ),
% 3.40/0.93      inference(renaming,[status(thm)],[c_631]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_896,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.40/0.93      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.40/0.93      | ~ m1_subset_1(X3,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X4,u1_struct_0(sK8))
% 3.40/0.93      | ~ l2_lattices(X1)
% 3.40/0.93      | v2_struct_0(X1)
% 3.40/0.93      | X3 != X2
% 3.40/0.93      | X4 != X0
% 3.40/0.93      | k1_lattices(X1,X2,X0) != X0
% 3.40/0.93      | k2_lattices(sK8,X3,X4) = X3
% 3.40/0.93      | sK8 != X1 ),
% 3.40/0.93      inference(resolution_lifted,[status(thm)],[c_13,c_632]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_897,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/0.93      | ~ l2_lattices(sK8)
% 3.40/0.93      | v2_struct_0(sK8)
% 3.40/0.93      | k1_lattices(sK8,X0,X1) != X1
% 3.40/0.93      | k2_lattices(sK8,X0,X1) = X0 ),
% 3.40/0.93      inference(unflattening,[status(thm)],[c_896]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_901,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 3.40/0.93      | k1_lattices(sK8,X0,X1) != X1
% 3.40/0.93      | k2_lattices(sK8,X0,X1) = X0 ),
% 3.40/0.93      inference(global_propositional_subsumption,
% 3.40/0.93                [status(thm)],
% 3.40/0.93                [c_897,c_41,c_38,c_68]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1589,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0_58,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(X1_58,u1_struct_0(sK8))
% 3.40/0.93      | k1_lattices(sK8,X0_58,X1_58) != X1_58
% 3.40/0.93      | k2_lattices(sK8,X0_58,X1_58) = X0_58 ),
% 3.40/0.93      inference(subtyping,[status(esa)],[c_901]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1858,plain,
% 3.40/0.93      ( k1_lattices(sK8,X0_58,X1_58) != X1_58
% 3.40/0.93      | k2_lattices(sK8,X0_58,X1_58) = X0_58
% 3.40/0.93      | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top
% 3.40/0.93      | m1_subset_1(X1_58,u1_struct_0(sK8)) != iProver_top ),
% 3.40/0.93      inference(predicate_to_equality,[status(thm)],[c_1589]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_6354,plain,
% 3.40/0.93      ( k2_lattices(sK8,sK10,sK10) = sK10
% 3.40/0.93      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_3094,c_1858]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_6357,plain,
% 3.40/0.93      ( k4_lattices(sK8,sK10,sK10) = sK10
% 3.40/0.93      | m1_subset_1(sK10,u1_struct_0(sK8)) != iProver_top ),
% 3.40/0.93      inference(demodulation,[status(thm)],[c_6354,c_5706]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_47,plain,
% 3.40/0.93      ( m1_subset_1(sK10,u1_struct_0(sK8)) = iProver_top ),
% 3.40/0.93      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_7390,plain,
% 3.40/0.93      ( k4_lattices(sK8,sK10,sK10) = sK10 ),
% 3.40/0.93      inference(global_propositional_subsumption,[status(thm)],[c_6357,c_47]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_4948,plain,
% 3.40/0.93      ( k1_lattices(sK8,k2_lattices(sK8,sK11,X0_58),k2_lattices(sK8,sK11,X1_58)) = k2_lattices(sK8,sK11,k1_lattices(sK8,X0_58,X1_58))
% 3.40/0.93      | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top
% 3.40/0.93      | m1_subset_1(X1_58,u1_struct_0(sK8)) != iProver_top ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1848,c_1861]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_5113,plain,
% 3.40/0.93      ( k1_lattices(sK8,k2_lattices(sK8,sK11,sK9),k2_lattices(sK8,sK11,X0_58)) = k2_lattices(sK8,sK11,k1_lattices(sK8,sK9,X0_58))
% 3.40/0.93      | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1850,c_4948]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_5221,plain,
% 3.40/0.93      ( k1_lattices(sK8,k2_lattices(sK8,sK11,sK9),k2_lattices(sK8,sK11,sK11)) = k2_lattices(sK8,sK11,k1_lattices(sK8,sK9,sK11)) ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1848,c_5113]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_2794,plain,
% 3.40/0.93      ( k1_lattices(sK8,sK9,sK11) = k3_lattices(sK8,sK9,sK11) ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1848,c_2029]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_2797,plain,
% 3.40/0.93      ( k1_lattices(sK8,sK9,sK11) = k3_lattices(sK8,sK9,sK10) ),
% 3.40/0.93      inference(light_normalisation,[status(thm)],[c_2794,c_1601]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_3370,plain,
% 3.40/0.93      ( k1_lattices(sK8,sK9,sK11) = k3_lattices(sK8,sK11,sK9) ),
% 3.40/0.93      inference(demodulation,[status(thm)],[c_3265,c_2797]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_3604,plain,
% 3.40/0.93      ( k1_lattices(sK8,sK9,sK11) = k3_lattices(sK8,sK10,sK9) ),
% 3.40/0.93      inference(demodulation,[status(thm)],[c_3603,c_3370]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_5227,plain,
% 3.40/0.93      ( k1_lattices(sK8,k2_lattices(sK8,sK11,sK9),k2_lattices(sK8,sK11,sK11)) = k2_lattices(sK8,sK11,k3_lattices(sK8,sK10,sK9)) ),
% 3.40/0.93      inference(light_normalisation,[status(thm)],[c_5221,c_3604]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_5485,plain,
% 3.40/0.93      ( k2_lattices(sK8,sK11,X0_58) = k4_lattices(sK8,sK11,X0_58)
% 3.40/0.93      | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1848,c_1856]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_5623,plain,
% 3.40/0.93      ( k2_lattices(sK8,sK11,sK9) = k4_lattices(sK8,sK11,sK9) ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1850,c_5485]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_3670,plain,
% 3.40/0.93      ( k4_lattices(sK8,sK11,X0_58) = k4_lattices(sK8,X0_58,sK11)
% 3.40/0.93      | m1_subset_1(X0_58,u1_struct_0(sK8)) != iProver_top ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1848,c_1854]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_3857,plain,
% 3.40/0.93      ( k4_lattices(sK8,sK11,sK9) = k4_lattices(sK8,sK9,sK11) ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1850,c_3670]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_34,negated_conjecture,
% 3.40/0.93      ( k4_lattices(sK8,sK9,sK10) = k4_lattices(sK8,sK9,sK11) ),
% 3.40/0.93      inference(cnf_transformation,[],[f107]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1600,negated_conjecture,
% 3.40/0.93      ( k4_lattices(sK8,sK9,sK10) = k4_lattices(sK8,sK9,sK11) ),
% 3.40/0.93      inference(subtyping,[status(esa)],[c_34]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_4001,plain,
% 3.40/0.93      ( k4_lattices(sK8,sK11,sK9) = k4_lattices(sK8,sK9,sK10) ),
% 3.40/0.93      inference(demodulation,[status(thm)],[c_3857,c_1600]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_4142,plain,
% 3.40/0.93      ( k4_lattices(sK8,sK10,sK9) = k4_lattices(sK8,sK11,sK9) ),
% 3.40/0.93      inference(demodulation,[status(thm)],[c_4141,c_4001]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_5625,plain,
% 3.40/0.93      ( k2_lattices(sK8,sK11,sK9) = k4_lattices(sK8,sK10,sK9) ),
% 3.40/0.93      inference(light_normalisation,[status(thm)],[c_5623,c_4142]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_5895,plain,
% 3.40/0.93      ( k2_lattices(sK8,sK9,sK11) = k4_lattices(sK8,sK9,sK11) ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1848,c_5487]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_4234,plain,
% 3.40/0.93      ( k4_lattices(sK8,sK10,sK9) = k4_lattices(sK8,sK9,sK11) ),
% 3.40/0.93      inference(demodulation,[status(thm)],[c_4142,c_3857]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_5900,plain,
% 3.40/0.93      ( k2_lattices(sK8,sK9,sK11) = k4_lattices(sK8,sK10,sK9) ),
% 3.40/0.93      inference(light_normalisation,[status(thm)],[c_5895,c_4234]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_2331,plain,
% 3.40/0.93      ( k1_lattices(sK8,k2_lattices(sK8,sK9,sK11),sK11) = sK11 ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1848,c_1972]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_7040,plain,
% 3.40/0.93      ( k1_lattices(sK8,k4_lattices(sK8,sK10,sK9),sK11) = sK11 ),
% 3.40/0.93      inference(demodulation,[status(thm)],[c_5900,c_2331]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_3093,plain,
% 3.40/0.93      ( k1_lattices(sK8,sK11,sK11) = sK11 ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1848,c_1853]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_6346,plain,
% 3.40/0.93      ( k2_lattices(sK8,sK11,sK11) = sK11
% 3.40/0.93      | m1_subset_1(sK11,u1_struct_0(sK8)) != iProver_top ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_3093,c_1858]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_5621,plain,
% 3.40/0.93      ( k2_lattices(sK8,sK11,sK11) = k4_lattices(sK8,sK11,sK11) ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1848,c_5485]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_6365,plain,
% 3.40/0.93      ( k4_lattices(sK8,sK11,sK11) = sK11
% 3.40/0.93      | m1_subset_1(sK11,u1_struct_0(sK8)) != iProver_top ),
% 3.40/0.93      inference(demodulation,[status(thm)],[c_6346,c_5621]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1604,plain,( X0_58 = X0_58 ),theory(equality) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1898,plain,
% 3.40/0.93      ( sK11 = sK11 ),
% 3.40/0.93      inference(instantiation,[status(thm)],[c_1604]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1954,plain,
% 3.40/0.93      ( ~ m1_subset_1(sK11,u1_struct_0(sK8))
% 3.40/0.93      | k1_lattices(sK8,sK11,sK11) = sK11 ),
% 3.40/0.93      inference(instantiation,[status(thm)],[c_1594]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1910,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0_58,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(sK11,u1_struct_0(sK8))
% 3.40/0.93      | k1_lattices(sK8,sK11,X0_58) != X0_58
% 3.40/0.93      | k2_lattices(sK8,sK11,X0_58) = sK11 ),
% 3.40/0.93      inference(instantiation,[status(thm)],[c_1589]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_2007,plain,
% 3.40/0.93      ( ~ m1_subset_1(sK11,u1_struct_0(sK8))
% 3.40/0.93      | k1_lattices(sK8,sK11,sK11) != sK11
% 3.40/0.93      | k2_lattices(sK8,sK11,sK11) = sK11 ),
% 3.40/0.93      inference(instantiation,[status(thm)],[c_1910]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1605,plain,
% 3.40/0.93      ( X0_58 != X1_58 | X2_58 != X1_58 | X2_58 = X0_58 ),
% 3.40/0.93      theory(equality) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1893,plain,
% 3.40/0.93      ( X0_58 != X1_58 | sK11 != X1_58 | sK11 = X0_58 ),
% 3.40/0.93      inference(instantiation,[status(thm)],[c_1605]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1895,plain,
% 3.40/0.93      ( X0_58 != sK11 | sK11 = X0_58 | sK11 != sK11 ),
% 3.40/0.93      inference(instantiation,[status(thm)],[c_1893]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1909,plain,
% 3.40/0.93      ( k2_lattices(sK8,sK11,X0_58) != sK11
% 3.40/0.93      | sK11 = k2_lattices(sK8,sK11,X0_58)
% 3.40/0.93      | sK11 != sK11 ),
% 3.40/0.93      inference(instantiation,[status(thm)],[c_1895]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_2085,plain,
% 3.40/0.93      ( k2_lattices(sK8,sK11,sK11) != sK11
% 3.40/0.93      | sK11 = k2_lattices(sK8,sK11,sK11)
% 3.40/0.93      | sK11 != sK11 ),
% 3.40/0.93      inference(instantiation,[status(thm)],[c_1909]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_2289,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0_58,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(sK11,u1_struct_0(sK8))
% 3.40/0.93      | k2_lattices(sK8,X0_58,sK11) = k4_lattices(sK8,X0_58,sK11) ),
% 3.40/0.93      inference(instantiation,[status(thm)],[c_1591]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_2955,plain,
% 3.40/0.93      ( ~ m1_subset_1(sK11,u1_struct_0(sK8))
% 3.40/0.93      | k2_lattices(sK8,sK11,sK11) = k4_lattices(sK8,sK11,sK11) ),
% 3.40/0.93      inference(instantiation,[status(thm)],[c_2289]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_2505,plain,
% 3.40/0.93      ( X0_58 != X1_58
% 3.40/0.93      | X0_58 = k2_lattices(sK8,sK11,sK11)
% 3.40/0.93      | k2_lattices(sK8,sK11,sK11) != X1_58 ),
% 3.40/0.93      inference(instantiation,[status(thm)],[c_1605]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_2954,plain,
% 3.40/0.93      ( X0_58 = k2_lattices(sK8,sK11,sK11)
% 3.40/0.93      | X0_58 != k4_lattices(sK8,sK11,sK11)
% 3.40/0.93      | k2_lattices(sK8,sK11,sK11) != k4_lattices(sK8,sK11,sK11) ),
% 3.40/0.93      inference(instantiation,[status(thm)],[c_2505]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_3740,plain,
% 3.40/0.93      ( k2_lattices(sK8,sK11,sK11) != k4_lattices(sK8,sK11,sK11)
% 3.40/0.93      | k4_lattices(sK8,sK11,sK11) = k2_lattices(sK8,sK11,sK11)
% 3.40/0.93      | k4_lattices(sK8,sK11,sK11) != k4_lattices(sK8,sK11,sK11) ),
% 3.40/0.93      inference(instantiation,[status(thm)],[c_2954]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_2812,plain,
% 3.40/0.93      ( ~ m1_subset_1(X0_58,u1_struct_0(sK8))
% 3.40/0.93      | ~ m1_subset_1(sK11,u1_struct_0(sK8))
% 3.40/0.93      | k4_lattices(sK8,X0_58,sK11) = k4_lattices(sK8,sK11,X0_58) ),
% 3.40/0.93      inference(instantiation,[status(thm)],[c_1593]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_3741,plain,
% 3.40/0.93      ( ~ m1_subset_1(sK11,u1_struct_0(sK8))
% 3.40/0.93      | k4_lattices(sK8,sK11,sK11) = k4_lattices(sK8,sK11,sK11) ),
% 3.40/0.93      inference(instantiation,[status(thm)],[c_2812]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1920,plain,
% 3.40/0.93      ( X0_58 != X1_58 | X0_58 = sK11 | sK11 != X1_58 ),
% 3.40/0.93      inference(instantiation,[status(thm)],[c_1605]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_1936,plain,
% 3.40/0.93      ( X0_58 != k2_lattices(sK8,sK11,X1_58)
% 3.40/0.93      | X0_58 = sK11
% 3.40/0.93      | sK11 != k2_lattices(sK8,sK11,X1_58) ),
% 3.40/0.93      inference(instantiation,[status(thm)],[c_1920]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_2261,plain,
% 3.40/0.93      ( X0_58 != k2_lattices(sK8,sK11,sK11)
% 3.40/0.93      | X0_58 = sK11
% 3.40/0.93      | sK11 != k2_lattices(sK8,sK11,sK11) ),
% 3.40/0.93      inference(instantiation,[status(thm)],[c_1936]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_5831,plain,
% 3.40/0.93      ( k4_lattices(sK8,sK11,sK11) != k2_lattices(sK8,sK11,sK11)
% 3.40/0.93      | k4_lattices(sK8,sK11,sK11) = sK11
% 3.40/0.93      | sK11 != k2_lattices(sK8,sK11,sK11) ),
% 3.40/0.93      inference(instantiation,[status(thm)],[c_2261]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_7452,plain,
% 3.40/0.93      ( k4_lattices(sK8,sK11,sK11) = sK11 ),
% 3.40/0.93      inference(global_propositional_subsumption,
% 3.40/0.93                [status(thm)],
% 3.40/0.93                [c_6365,c_35,c_1898,c_1954,c_2007,c_2085,c_2955,c_3740,
% 3.40/0.93                 c_3741,c_5831]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_7455,plain,
% 3.40/0.93      ( k2_lattices(sK8,sK11,sK11) = sK11 ),
% 3.40/0.93      inference(demodulation,[status(thm)],[c_7452,c_5621]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_5222,plain,
% 3.40/0.93      ( k1_lattices(sK8,k2_lattices(sK8,sK11,sK9),k2_lattices(sK8,sK11,sK10)) = k2_lattices(sK8,sK11,k1_lattices(sK8,sK9,sK10)) ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1849,c_5113]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_5226,plain,
% 3.40/0.93      ( k1_lattices(sK8,k2_lattices(sK8,sK11,sK9),k2_lattices(sK8,sK11,sK10)) = k2_lattices(sK8,sK11,k3_lattices(sK8,sK10,sK9)) ),
% 3.40/0.93      inference(light_normalisation,[status(thm)],[c_5222,c_3605]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_5622,plain,
% 3.40/0.93      ( k2_lattices(sK8,sK11,sK10) = k4_lattices(sK8,sK11,sK10) ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1849,c_5485]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_3856,plain,
% 3.40/0.93      ( k4_lattices(sK8,sK10,sK11) = k4_lattices(sK8,sK11,sK10) ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1849,c_3670]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_5626,plain,
% 3.40/0.93      ( k2_lattices(sK8,sK11,sK10) = k4_lattices(sK8,sK10,sK11) ),
% 3.40/0.93      inference(light_normalisation,[status(thm)],[c_5622,c_3856]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_6064,plain,
% 3.40/0.93      ( k1_lattices(sK8,k4_lattices(sK8,sK10,sK9),k2_lattices(sK8,sK10,sK11)) = k2_lattices(sK8,sK10,k1_lattices(sK8,sK9,sK11)) ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1848,c_6060]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_5705,plain,
% 3.40/0.93      ( k2_lattices(sK8,sK10,sK11) = k4_lattices(sK8,sK10,sK11) ),
% 3.40/0.93      inference(superposition,[status(thm)],[c_1848,c_5486]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_6070,plain,
% 3.40/0.93      ( k1_lattices(sK8,k4_lattices(sK8,sK10,sK9),k4_lattices(sK8,sK10,sK11)) = k2_lattices(sK8,sK10,k3_lattices(sK8,sK10,sK9)) ),
% 3.40/0.93      inference(light_normalisation,[status(thm)],[c_6064,c_3604,c_5705]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_8076,plain,
% 3.40/0.93      ( k2_lattices(sK8,sK10,k3_lattices(sK8,sK10,sK9)) = k2_lattices(sK8,sK11,k3_lattices(sK8,sK10,sK9)) ),
% 3.40/0.93      inference(light_normalisation,
% 3.40/0.93                [status(thm)],
% 3.40/0.93                [c_5226,c_5226,c_5625,c_5626,c_6070]) ).
% 3.40/0.93  
% 3.40/0.93  cnf(c_8132,plain,
% 3.40/0.93      ( k2_lattices(sK8,sK10,k3_lattices(sK8,sK10,sK9)) = sK11 ),
% 3.40/0.93      inference(light_normalisation,
% 3.40/0.93                [status(thm)],
% 3.40/0.93                [c_5227,c_5227,c_5625,c_7040,c_7455,c_8076]) ).
% 3.40/0.94  
% 3.40/0.94  cnf(c_8806,plain,
% 3.40/0.94      ( sK11 = sK10 ),
% 3.40/0.94      inference(light_normalisation,
% 3.40/0.94                [status(thm)],
% 3.40/0.94                [c_6069,c_6069,c_7039,c_7390,c_8132]) ).
% 3.40/0.94  
% 3.40/0.94  cnf(c_32,negated_conjecture,
% 3.40/0.94      ( sK10 != sK11 ),
% 3.40/0.94      inference(cnf_transformation,[],[f109]) ).
% 3.40/0.94  
% 3.40/0.94  cnf(c_1602,negated_conjecture,
% 3.40/0.94      ( sK10 != sK11 ),
% 3.40/0.94      inference(subtyping,[status(esa)],[c_32]) ).
% 3.40/0.94  
% 3.40/0.94  cnf(c_8849,plain,
% 3.40/0.94      ( sK10 != sK10 ),
% 3.40/0.94      inference(demodulation,[status(thm)],[c_8806,c_1602]) ).
% 3.40/0.94  
% 3.40/0.94  cnf(c_8850,plain,
% 3.40/0.94      ( $false ),
% 3.40/0.94      inference(equality_resolution_simp,[status(thm)],[c_8849]) ).
% 3.40/0.94  
% 3.40/0.94  
% 3.40/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 3.40/0.94  
% 3.40/0.94  ------                               Statistics
% 3.40/0.94  
% 3.40/0.94  ------ General
% 3.40/0.94  
% 3.40/0.94  abstr_ref_over_cycles:                  0
% 3.40/0.94  abstr_ref_under_cycles:                 0
% 3.40/0.94  gc_basic_clause_elim:                   0
% 3.40/0.94  forced_gc_time:                         0
% 3.40/0.94  parsing_time:                           0.01
% 3.40/0.94  unif_index_cands_time:                  0.
% 3.40/0.94  unif_index_add_time:                    0.
% 3.40/0.94  orderings_time:                         0.
% 3.40/0.94  out_proof_time:                         0.017
% 3.40/0.94  total_time:                             0.333
% 3.40/0.94  num_of_symbols:                         61
% 3.40/0.94  num_of_terms:                           10750
% 3.40/0.94  
% 3.40/0.94  ------ Preprocessing
% 3.40/0.94  
% 3.40/0.94  num_of_splits:                          0
% 3.40/0.94  num_of_split_atoms:                     0
% 3.40/0.94  num_of_reused_defs:                     0
% 3.40/0.94  num_eq_ax_congr_red:                    28
% 3.40/0.94  num_of_sem_filtered_clauses:            1
% 3.40/0.94  num_of_subtypes:                        3
% 3.40/0.94  monotx_restored_types:                  0
% 3.40/0.94  sat_num_of_epr_types:                   0
% 3.40/0.94  sat_num_of_non_cyclic_types:            0
% 3.40/0.94  sat_guarded_non_collapsed_types:        1
% 3.40/0.94  num_pure_diseq_elim:                    0
% 3.40/0.94  simp_replaced_by:                       0
% 3.40/0.94  res_preprocessed:                       107
% 3.40/0.94  prep_upred:                             0
% 3.40/0.94  prep_unflattend:                        51
% 3.40/0.94  smt_new_axioms:                         0
% 3.40/0.94  pred_elim_cands:                        1
% 3.40/0.94  pred_elim:                              12
% 3.40/0.94  pred_elim_cl:                           24
% 3.40/0.94  pred_elim_cycles:                       17
% 3.40/0.94  merged_defs:                            0
% 3.40/0.94  merged_defs_ncl:                        0
% 3.40/0.94  bin_hyper_res:                          0
% 3.40/0.94  prep_cycles:                            4
% 3.40/0.94  pred_elim_time:                         0.023
% 3.40/0.94  splitting_time:                         0.
% 3.40/0.94  sem_filter_time:                        0.
% 3.40/0.94  monotx_time:                            0.
% 3.40/0.94  subtype_inf_time:                       0.
% 3.40/0.94  
% 3.40/0.94  ------ Problem properties
% 3.40/0.94  
% 3.40/0.94  clauses:                                17
% 3.40/0.94  conjectures:                            6
% 3.40/0.94  epr:                                    1
% 3.40/0.94  horn:                                   17
% 3.40/0.94  ground:                                 6
% 3.40/0.94  unary:                                  6
% 3.40/0.94  binary:                                 1
% 3.40/0.94  lits:                                   42
% 3.40/0.94  lits_eq:                                15
% 3.40/0.94  fd_pure:                                0
% 3.40/0.94  fd_pseudo:                              0
% 3.40/0.94  fd_cond:                                0
% 3.40/0.94  fd_pseudo_cond:                         0
% 3.40/0.94  ac_symbols:                             0
% 3.40/0.94  
% 3.40/0.94  ------ Propositional Solver
% 3.40/0.94  
% 3.40/0.94  prop_solver_calls:                      34
% 3.40/0.94  prop_fast_solver_calls:                 1146
% 3.40/0.94  smt_solver_calls:                       0
% 3.40/0.94  smt_fast_solver_calls:                  0
% 3.40/0.94  prop_num_of_clauses:                    4223
% 3.40/0.94  prop_preprocess_simplified:             9025
% 3.40/0.94  prop_fo_subsumed:                       49
% 3.40/0.94  prop_solver_time:                       0.
% 3.40/0.94  smt_solver_time:                        0.
% 3.40/0.94  smt_fast_solver_time:                   0.
% 3.40/0.94  prop_fast_solver_time:                  0.
% 3.40/0.94  prop_unsat_core_time:                   0.
% 3.40/0.94  
% 3.40/0.94  ------ QBF
% 3.40/0.94  
% 3.40/0.94  qbf_q_res:                              0
% 3.40/0.94  qbf_num_tautologies:                    0
% 3.40/0.94  qbf_prep_cycles:                        0
% 3.40/0.94  
% 3.40/0.94  ------ BMC1
% 3.40/0.94  
% 3.40/0.94  bmc1_current_bound:                     -1
% 3.40/0.94  bmc1_last_solved_bound:                 -1
% 3.40/0.94  bmc1_unsat_core_size:                   -1
% 3.40/0.94  bmc1_unsat_core_parents_size:           -1
% 3.40/0.94  bmc1_merge_next_fun:                    0
% 3.40/0.94  bmc1_unsat_core_clauses_time:           0.
% 3.40/0.94  
% 3.40/0.94  ------ Instantiation
% 3.40/0.94  
% 3.40/0.94  inst_num_of_clauses:                    1732
% 3.40/0.94  inst_num_in_passive:                    695
% 3.40/0.94  inst_num_in_active:                     591
% 3.40/0.94  inst_num_in_unprocessed:                446
% 3.40/0.94  inst_num_of_loops:                      650
% 3.40/0.94  inst_num_of_learning_restarts:          0
% 3.40/0.94  inst_num_moves_active_passive:          51
% 3.40/0.94  inst_lit_activity:                      0
% 3.40/0.94  inst_lit_activity_moves:                0
% 3.40/0.94  inst_num_tautologies:                   0
% 3.40/0.94  inst_num_prop_implied:                  0
% 3.40/0.94  inst_num_existing_simplified:           0
% 3.40/0.94  inst_num_eq_res_simplified:             0
% 3.40/0.94  inst_num_child_elim:                    0
% 3.40/0.94  inst_num_of_dismatching_blockings:      896
% 3.40/0.94  inst_num_of_non_proper_insts:           1984
% 3.40/0.94  inst_num_of_duplicates:                 0
% 3.40/0.94  inst_inst_num_from_inst_to_res:         0
% 3.40/0.94  inst_dismatching_checking_time:         0.
% 3.40/0.94  
% 3.40/0.94  ------ Resolution
% 3.40/0.94  
% 3.40/0.94  res_num_of_clauses:                     0
% 3.40/0.94  res_num_in_passive:                     0
% 3.40/0.94  res_num_in_active:                      0
% 3.40/0.94  res_num_of_loops:                       111
% 3.40/0.94  res_forward_subset_subsumed:            89
% 3.40/0.94  res_backward_subset_subsumed:           0
% 3.40/0.94  res_forward_subsumed:                   0
% 3.40/0.94  res_backward_subsumed:                  0
% 3.40/0.94  res_forward_subsumption_resolution:     0
% 3.40/0.94  res_backward_subsumption_resolution:    0
% 3.40/0.94  res_clause_to_clause_subsumption:       643
% 3.40/0.94  res_orphan_elimination:                 0
% 3.40/0.94  res_tautology_del:                      165
% 3.40/0.94  res_num_eq_res_simplified:              0
% 3.40/0.94  res_num_sel_changes:                    0
% 3.40/0.94  res_moves_from_active_to_pass:          0
% 3.40/0.94  
% 3.40/0.94  ------ Superposition
% 3.40/0.94  
% 3.40/0.94  sup_time_total:                         0.
% 3.40/0.94  sup_time_generating:                    0.
% 3.40/0.94  sup_time_sim_full:                      0.
% 3.40/0.94  sup_time_sim_immed:                     0.
% 3.40/0.94  
% 3.40/0.94  sup_num_of_clauses:                     147
% 3.40/0.94  sup_num_in_active:                      46
% 3.40/0.94  sup_num_in_passive:                     101
% 3.40/0.94  sup_num_of_loops:                       128
% 3.40/0.94  sup_fw_superposition:                   151
% 3.40/0.94  sup_bw_superposition:                   54
% 3.40/0.94  sup_immediate_simplified:               71
% 3.40/0.94  sup_given_eliminated:                   0
% 3.40/0.94  comparisons_done:                       0
% 3.40/0.94  comparisons_avoided:                    0
% 3.40/0.94  
% 3.40/0.94  ------ Simplifications
% 3.40/0.94  
% 3.40/0.94  
% 3.40/0.94  sim_fw_subset_subsumed:                 9
% 3.40/0.94  sim_bw_subset_subsumed:                 0
% 3.40/0.94  sim_fw_subsumed:                        2
% 3.40/0.94  sim_bw_subsumed:                        0
% 3.40/0.94  sim_fw_subsumption_res:                 0
% 3.40/0.94  sim_bw_subsumption_res:                 0
% 3.40/0.94  sim_tautology_del:                      0
% 3.40/0.94  sim_eq_tautology_del:                   10
% 3.40/0.94  sim_eq_res_simp:                        0
% 3.40/0.94  sim_fw_demodulated:                     15
% 3.40/0.94  sim_bw_demodulated:                     82
% 3.40/0.94  sim_light_normalised:                   62
% 3.40/0.94  sim_joinable_taut:                      0
% 3.40/0.94  sim_joinable_simp:                      0
% 3.40/0.94  sim_ac_normalised:                      0
% 3.40/0.94  sim_smt_subsumption:                    0
% 3.40/0.94  
%------------------------------------------------------------------------------
