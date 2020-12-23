%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:15 EST 2020

% Result     : Theorem 35.55s
% Output     : CNFRefutation 35.55s
% Verified   : 
% Statistics : Number of formulae       :  180 (3542 expanded)
%              Number of clauses        :  119 ( 778 expanded)
%              Number of leaves         :   17 (1218 expanded)
%              Depth                    :   26
%              Number of atoms          :  679 (27796 expanded)
%              Number of equality atoms :  204 (9245 expanded)
%              Maximal formula depth    :   13 (   5 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( X2 != X3
          & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
          & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sK5 != X2
        & k3_lattices(X0,X1,sK5) = k3_lattices(X0,X1,X2)
        & k4_lattices(X0,X1,sK5) = k4_lattices(X0,X1,X2)
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
              & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( sK4 != X3
            & k3_lattices(X0,X1,sK4) = k3_lattices(X0,X1,X3)
            & k4_lattices(X0,X1,sK4) = k4_lattices(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
                & k3_lattices(X0,sK3,X2) = k3_lattices(X0,sK3,X3)
                & k4_lattices(X0,sK3,X2) = k4_lattices(X0,sK3,X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
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
                  & k3_lattices(sK2,X1,X2) = k3_lattices(sK2,X1,X3)
                  & k4_lattices(sK2,X1,X2) = k4_lattices(sK2,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(sK2)) )
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l3_lattices(sK2)
      & v11_lattices(sK2)
      & v10_lattices(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( sK4 != sK5
    & k3_lattices(sK2,sK3,sK4) = k3_lattices(sK2,sK3,sK5)
    & k4_lattices(sK2,sK3,sK4) = k4_lattices(sK2,sK3,sK5)
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l3_lattices(sK2)
    & v11_lattices(sK2)
    & v10_lattices(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f30,f39,f38,f37,f36])).

fof(f61,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    k4_lattices(sK2,sK3,sK4) = k4_lattices(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v8_lattices(X0)
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
       => ( v8_lattices(X0)
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
       => ( v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f15,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f14])).

fof(f43,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    v10_lattices(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f56,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f60,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f18,plain,(
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

fof(f19,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k1_lattices(X0,k2_lattices(X0,X1,sK1(X0)),sK1(X0)) != sK1(X0)
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK0(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( k1_lattices(X0,k2_lattices(X0,sK0(X0),sK1(X0)),sK1(X0)) != sK1(X0)
            & m1_subset_1(sK1(X0),u1_struct_0(X0))
            & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).

fof(f46,plain,(
    ! [X4,X0,X3] :
      ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f44,plain,(
    ! [X0] :
      ( v8_lattices(X0)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
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
                 => k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,(
    v11_lattices(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    k3_lattices(sK2,sK3,sK4) = k3_lattices(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_515,plain,
    ( X0_49 != X1_49
    | X2_49 != X1_49
    | X2_49 = X0_49 ),
    theory(equality)).

cnf(c_82503,plain,
    ( X0_49 != X1_49
    | sK4 != X1_49
    | sK4 = X0_49 ),
    inference(instantiation,[status(thm)],[c_515])).

cnf(c_82681,plain,
    ( X0_49 != sK4
    | sK4 = X0_49
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_82503])).

cnf(c_127738,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_82681])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_508,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_677,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_17,negated_conjecture,
    ( k4_lattices(sK2,sK3,sK4) = k4_lattices(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_510,negated_conjecture,
    ( k4_lattices(sK2,sK3,sK4) = k4_lattices(sK2,sK3,sK5) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_23,negated_conjecture,
    ( v10_lattices(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_279,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_23])).

cnf(c_280,plain,
    ( v6_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_279])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_21,negated_conjecture,
    ( l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_70,plain,
    ( v6_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_282,plain,
    ( v6_lattices(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_280,c_24,c_23,c_21,c_70])).

cnf(c_328,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_282])).

cnf(c_329,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k4_lattices(sK2,X0,X1),u1_struct_0(sK2))
    | ~ l1_lattices(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_328])).

cnf(c_11,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_42,plain,
    ( l1_lattices(sK2)
    | ~ l3_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_333,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(k4_lattices(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_329,c_24,c_21,c_42])).

cnf(c_504,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK2))
    | m1_subset_1(k4_lattices(sK2,X0_49,X1_49),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_333])).

cnf(c_681,plain,
    ( m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k4_lattices(sK2,X0_49,X1_49),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_504])).

cnf(c_1871,plain,
    ( m1_subset_1(k4_lattices(sK2,sK3,sK4),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_510,c_681])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_507,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_678,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_507])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_307,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_282])).

cnf(c_308,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_lattices(sK2)
    | v2_struct_0(sK2)
    | k4_lattices(sK2,X0,X1) = k2_lattices(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_307])).

cnf(c_312,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k4_lattices(sK2,X0,X1) = k2_lattices(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_308,c_24,c_21,c_42])).

cnf(c_505,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK2))
    | k4_lattices(sK2,X0_49,X1_49) = k2_lattices(sK2,X0_49,X1_49) ),
    inference(subtyping,[status(esa)],[c_312])).

cnf(c_680,plain,
    ( k4_lattices(sK2,X0_49,X1_49) = k2_lattices(sK2,X0_49,X1_49)
    | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_1308,plain,
    ( k4_lattices(sK2,sK3,X0_49) = k2_lattices(sK2,sK3,X0_49)
    | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_678,c_680])).

cnf(c_1822,plain,
    ( k4_lattices(sK2,sK3,sK4) = k2_lattices(sK2,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_677,c_1308])).

cnf(c_1891,plain,
    ( m1_subset_1(k2_lattices(sK2,sK3,sK4),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1871,c_1822])).

cnf(c_29,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_31,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2309,plain,
    ( m1_subset_1(k2_lattices(sK2,sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1891,c_29,c_31])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_268,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_23])).

cnf(c_269,plain,
    ( v4_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_268])).

cnf(c_67,plain,
    ( v4_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_271,plain,
    ( v4_lattices(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_269,c_24,c_23,c_21,c_67])).

cnf(c_357,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_271])).

cnf(c_358,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l2_lattices(sK2)
    | v2_struct_0(sK2)
    | k1_lattices(sK2,X0,X1) = k3_lattices(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_10,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_45,plain,
    ( l2_lattices(sK2)
    | ~ l3_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k1_lattices(sK2,X0,X1) = k3_lattices(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_358,c_24,c_21,c_45])).

cnf(c_503,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK2))
    | k1_lattices(sK2,X0_49,X1_49) = k3_lattices(sK2,X0_49,X1_49) ),
    inference(subtyping,[status(esa)],[c_362])).

cnf(c_682,plain,
    ( k1_lattices(sK2,X0_49,X1_49) = k3_lattices(sK2,X0_49,X1_49)
    | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_503])).

cnf(c_2555,plain,
    ( k1_lattices(sK2,k2_lattices(sK2,sK3,sK4),X0_49) = k3_lattices(sK2,k2_lattices(sK2,sK3,sK4),X0_49)
    | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2309,c_682])).

cnf(c_36798,plain,
    ( k1_lattices(sK2,k2_lattices(sK2,sK3,sK4),sK4) = k3_lattices(sK2,k2_lattices(sK2,sK3,sK4),sK4) ),
    inference(superposition,[status(thm)],[c_677,c_2555])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v8_lattices(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_413,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v8_lattices(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_414,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l3_lattices(sK2)
    | ~ v8_lattices(sK2)
    | k1_lattices(sK2,k2_lattices(sK2,X0,X1),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v8_lattices(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_73,plain,
    ( ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2)
    | v8_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_418,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k1_lattices(sK2,k2_lattices(sK2,X0,X1),X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_414,c_24,c_23,c_21,c_73])).

cnf(c_501,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK2))
    | k1_lattices(sK2,k2_lattices(sK2,X0_49,X1_49),X1_49) = X1_49 ),
    inference(subtyping,[status(esa)],[c_418])).

cnf(c_684,plain,
    ( k1_lattices(sK2,k2_lattices(sK2,X0_49,X1_49),X1_49) = X1_49
    | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_501])).

cnf(c_850,plain,
    ( k1_lattices(sK2,k2_lattices(sK2,sK3,X0_49),X0_49) = X0_49
    | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_678,c_684])).

cnf(c_1173,plain,
    ( k1_lattices(sK2,k2_lattices(sK2,sK3,sK4),sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_677,c_850])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_378,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_271])).

cnf(c_379,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l2_lattices(sK2)
    | v2_struct_0(sK2)
    | k3_lattices(sK2,X0,X1) = k3_lattices(sK2,X1,X0) ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_383,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k3_lattices(sK2,X0,X1) = k3_lattices(sK2,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_379,c_24,c_21,c_45])).

cnf(c_502,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK2))
    | k3_lattices(sK2,X0_49,X1_49) = k3_lattices(sK2,X1_49,X0_49) ),
    inference(subtyping,[status(esa)],[c_383])).

cnf(c_683,plain,
    ( k3_lattices(sK2,X0_49,X1_49) = k3_lattices(sK2,X1_49,X0_49)
    | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_502])).

cnf(c_3531,plain,
    ( k3_lattices(sK2,sK4,X0_49) = k3_lattices(sK2,X0_49,sK4)
    | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_677,c_683])).

cnf(c_3858,plain,
    ( k3_lattices(sK2,sK4,k2_lattices(sK2,sK3,sK4)) = k3_lattices(sK2,k2_lattices(sK2,sK3,sK4),sK4) ),
    inference(superposition,[status(thm)],[c_2309,c_3531])).

cnf(c_36810,plain,
    ( k3_lattices(sK2,sK4,k2_lattices(sK2,sK3,sK4)) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_36798,c_1173,c_3858])).

cnf(c_509,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_676,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_36797,plain,
    ( k1_lattices(sK2,k2_lattices(sK2,sK3,sK4),sK5) = k3_lattices(sK2,k2_lattices(sK2,sK3,sK4),sK5) ),
    inference(superposition,[status(thm)],[c_676,c_2555])).

cnf(c_1821,plain,
    ( k4_lattices(sK2,sK3,sK5) = k2_lattices(sK2,sK3,sK5) ),
    inference(superposition,[status(thm)],[c_676,c_1308])).

cnf(c_1933,plain,
    ( k4_lattices(sK2,sK3,sK4) = k2_lattices(sK2,sK3,sK5) ),
    inference(demodulation,[status(thm)],[c_1821,c_510])).

cnf(c_1934,plain,
    ( k2_lattices(sK2,sK3,sK4) = k2_lattices(sK2,sK3,sK5) ),
    inference(light_normalisation,[status(thm)],[c_1933,c_1822])).

cnf(c_1172,plain,
    ( k1_lattices(sK2,k2_lattices(sK2,sK3,sK5),sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_676,c_850])).

cnf(c_2088,plain,
    ( k1_lattices(sK2,k2_lattices(sK2,sK3,sK4),sK5) = sK5 ),
    inference(demodulation,[status(thm)],[c_1934,c_1172])).

cnf(c_3530,plain,
    ( k3_lattices(sK2,sK5,X0_49) = k3_lattices(sK2,X0_49,sK5)
    | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_676,c_683])).

cnf(c_3553,plain,
    ( k3_lattices(sK2,sK5,k2_lattices(sK2,sK3,sK4)) = k3_lattices(sK2,k2_lattices(sK2,sK3,sK4),sK5) ),
    inference(superposition,[status(thm)],[c_2309,c_3530])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k3_lattices(X1,X2,X0),k3_lattices(X1,X2,X3)) = k3_lattices(X1,X2,k4_lattices(X1,X0,X3)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,negated_conjecture,
    ( v11_lattices(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_239,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k3_lattices(X1,X2,X0),k3_lattices(X1,X2,X3)) = k3_lattices(X1,X2,k4_lattices(X1,X0,X3))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_240,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2)
    | k4_lattices(sK2,k3_lattices(sK2,X1,X2),k3_lattices(sK2,X1,X0)) = k3_lattices(sK2,X1,k4_lattices(sK2,X2,X0)) ),
    inference(unflattening,[status(thm)],[c_239])).

cnf(c_244,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k4_lattices(sK2,k3_lattices(sK2,X1,X2),k3_lattices(sK2,X1,X0)) = k3_lattices(sK2,X1,k4_lattices(sK2,X2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_240,c_24,c_23,c_21])).

cnf(c_245,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | k4_lattices(sK2,k3_lattices(sK2,X2,X0),k3_lattices(sK2,X2,X1)) = k3_lattices(sK2,X2,k4_lattices(sK2,X0,X1)) ),
    inference(renaming,[status(thm)],[c_244])).

cnf(c_506,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK2))
    | k4_lattices(sK2,k3_lattices(sK2,X2_49,X0_49),k3_lattices(sK2,X2_49,X1_49)) = k3_lattices(sK2,X2_49,k4_lattices(sK2,X0_49,X1_49)) ),
    inference(subtyping,[status(esa)],[c_245])).

cnf(c_679,plain,
    ( k4_lattices(sK2,k3_lattices(sK2,X0_49,X1_49),k3_lattices(sK2,X0_49,X2_49)) = k3_lattices(sK2,X0_49,k4_lattices(sK2,X1_49,X2_49))
    | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_506])).

cnf(c_912,plain,
    ( k4_lattices(sK2,k3_lattices(sK2,X0_49,X1_49),k3_lattices(sK2,X0_49,sK4)) = k3_lattices(sK2,X0_49,k4_lattices(sK2,X1_49,sK4))
    | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_677,c_679])).

cnf(c_2532,plain,
    ( k4_lattices(sK2,k3_lattices(sK2,sK5,X0_49),k3_lattices(sK2,sK5,sK4)) = k3_lattices(sK2,sK5,k4_lattices(sK2,X0_49,sK4))
    | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_676,c_912])).

cnf(c_3550,plain,
    ( k3_lattices(sK2,sK5,sK4) = k3_lattices(sK2,sK4,sK5) ),
    inference(superposition,[status(thm)],[c_677,c_3530])).

cnf(c_4190,plain,
    ( k4_lattices(sK2,k3_lattices(sK2,sK5,X0_49),k3_lattices(sK2,sK4,sK5)) = k3_lattices(sK2,sK5,k4_lattices(sK2,X0_49,sK4))
    | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2532,c_3550])).

cnf(c_4196,plain,
    ( k4_lattices(sK2,k3_lattices(sK2,sK5,sK3),k3_lattices(sK2,sK4,sK5)) = k3_lattices(sK2,sK5,k4_lattices(sK2,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_678,c_4190])).

cnf(c_911,plain,
    ( k4_lattices(sK2,k3_lattices(sK2,X0_49,X1_49),k3_lattices(sK2,X0_49,sK5)) = k3_lattices(sK2,X0_49,k4_lattices(sK2,X1_49,sK5))
    | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_676,c_679])).

cnf(c_1293,plain,
    ( k4_lattices(sK2,k3_lattices(sK2,sK4,X0_49),k3_lattices(sK2,sK4,sK5)) = k3_lattices(sK2,sK4,k4_lattices(sK2,X0_49,sK5))
    | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_677,c_911])).

cnf(c_2453,plain,
    ( k4_lattices(sK2,k3_lattices(sK2,sK4,sK3),k3_lattices(sK2,sK4,sK5)) = k3_lattices(sK2,sK4,k4_lattices(sK2,sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_678,c_1293])).

cnf(c_2087,plain,
    ( k4_lattices(sK2,sK3,sK5) = k2_lattices(sK2,sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_1934,c_1821])).

cnf(c_2456,plain,
    ( k4_lattices(sK2,k3_lattices(sK2,sK4,sK3),k3_lattices(sK2,sK4,sK5)) = k3_lattices(sK2,sK4,k2_lattices(sK2,sK3,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_2453,c_2087])).

cnf(c_3856,plain,
    ( k3_lattices(sK2,sK4,sK3) = k3_lattices(sK2,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_678,c_3531])).

cnf(c_3551,plain,
    ( k3_lattices(sK2,sK5,sK3) = k3_lattices(sK2,sK3,sK5) ),
    inference(superposition,[status(thm)],[c_678,c_3530])).

cnf(c_16,negated_conjecture,
    ( k3_lattices(sK2,sK3,sK4) = k3_lattices(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_511,negated_conjecture,
    ( k3_lattices(sK2,sK3,sK4) = k3_lattices(sK2,sK3,sK5) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_3613,plain,
    ( k3_lattices(sK2,sK5,sK3) = k3_lattices(sK2,sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_3551,c_511])).

cnf(c_3878,plain,
    ( k3_lattices(sK2,sK4,sK3) = k3_lattices(sK2,sK5,sK3) ),
    inference(demodulation,[status(thm)],[c_3856,c_3613])).

cnf(c_4199,plain,
    ( k3_lattices(sK2,sK5,k2_lattices(sK2,sK3,sK4)) = k3_lattices(sK2,sK4,k2_lattices(sK2,sK3,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_4196,c_1822,c_2456,c_3878])).

cnf(c_5748,plain,
    ( k3_lattices(sK2,k2_lattices(sK2,sK3,sK4),sK5) = k3_lattices(sK2,sK4,k2_lattices(sK2,sK3,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_3553,c_3553,c_4199])).

cnf(c_36811,plain,
    ( k3_lattices(sK2,sK4,k2_lattices(sK2,sK3,sK4)) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_36797,c_2088,c_5748])).

cnf(c_37116,plain,
    ( sK5 = sK4 ),
    inference(superposition,[status(thm)],[c_36810,c_36811])).

cnf(c_514,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_862,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_514])).

cnf(c_15,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_512,negated_conjecture,
    ( sK4 != sK5 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_127738,c_37116,c_862,c_512])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:48:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 35.55/4.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.55/4.99  
% 35.55/4.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.55/4.99  
% 35.55/4.99  ------  iProver source info
% 35.55/4.99  
% 35.55/4.99  git: date: 2020-06-30 10:37:57 +0100
% 35.55/4.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.55/4.99  git: non_committed_changes: false
% 35.55/4.99  git: last_make_outside_of_git: false
% 35.55/4.99  
% 35.55/4.99  ------ 
% 35.55/4.99  
% 35.55/4.99  ------ Input Options
% 35.55/4.99  
% 35.55/4.99  --out_options                           all
% 35.55/4.99  --tptp_safe_out                         true
% 35.55/4.99  --problem_path                          ""
% 35.55/4.99  --include_path                          ""
% 35.55/4.99  --clausifier                            res/vclausify_rel
% 35.55/4.99  --clausifier_options                    ""
% 35.55/4.99  --stdin                                 false
% 35.55/4.99  --stats_out                             all
% 35.55/4.99  
% 35.55/4.99  ------ General Options
% 35.55/4.99  
% 35.55/4.99  --fof                                   false
% 35.55/4.99  --time_out_real                         305.
% 35.55/4.99  --time_out_virtual                      -1.
% 35.55/4.99  --symbol_type_check                     false
% 35.55/4.99  --clausify_out                          false
% 35.55/4.99  --sig_cnt_out                           false
% 35.55/4.99  --trig_cnt_out                          false
% 35.55/4.99  --trig_cnt_out_tolerance                1.
% 35.55/4.99  --trig_cnt_out_sk_spl                   false
% 35.55/4.99  --abstr_cl_out                          false
% 35.55/4.99  
% 35.55/4.99  ------ Global Options
% 35.55/4.99  
% 35.55/4.99  --schedule                              default
% 35.55/4.99  --add_important_lit                     false
% 35.55/4.99  --prop_solver_per_cl                    1000
% 35.55/4.99  --min_unsat_core                        false
% 35.55/4.99  --soft_assumptions                      false
% 35.55/4.99  --soft_lemma_size                       3
% 35.55/4.99  --prop_impl_unit_size                   0
% 35.55/4.99  --prop_impl_unit                        []
% 35.55/4.99  --share_sel_clauses                     true
% 35.55/4.99  --reset_solvers                         false
% 35.55/4.99  --bc_imp_inh                            [conj_cone]
% 35.55/4.99  --conj_cone_tolerance                   3.
% 35.55/4.99  --extra_neg_conj                        none
% 35.55/4.99  --large_theory_mode                     true
% 35.55/4.99  --prolific_symb_bound                   200
% 35.55/4.99  --lt_threshold                          2000
% 35.55/4.99  --clause_weak_htbl                      true
% 35.55/4.99  --gc_record_bc_elim                     false
% 35.55/4.99  
% 35.55/4.99  ------ Preprocessing Options
% 35.55/4.99  
% 35.55/4.99  --preprocessing_flag                    true
% 35.55/4.99  --time_out_prep_mult                    0.1
% 35.55/4.99  --splitting_mode                        input
% 35.55/4.99  --splitting_grd                         true
% 35.55/4.99  --splitting_cvd                         false
% 35.55/4.99  --splitting_cvd_svl                     false
% 35.55/4.99  --splitting_nvd                         32
% 35.55/4.99  --sub_typing                            true
% 35.55/4.99  --prep_gs_sim                           true
% 35.55/4.99  --prep_unflatten                        true
% 35.55/4.99  --prep_res_sim                          true
% 35.55/4.99  --prep_upred                            true
% 35.55/4.99  --prep_sem_filter                       exhaustive
% 35.55/4.99  --prep_sem_filter_out                   false
% 35.55/4.99  --pred_elim                             true
% 35.55/4.99  --res_sim_input                         true
% 35.55/4.99  --eq_ax_congr_red                       true
% 35.55/4.99  --pure_diseq_elim                       true
% 35.55/4.99  --brand_transform                       false
% 35.55/4.99  --non_eq_to_eq                          false
% 35.55/4.99  --prep_def_merge                        true
% 35.55/4.99  --prep_def_merge_prop_impl              false
% 35.55/4.99  --prep_def_merge_mbd                    true
% 35.55/4.99  --prep_def_merge_tr_red                 false
% 35.55/4.99  --prep_def_merge_tr_cl                  false
% 35.55/4.99  --smt_preprocessing                     true
% 35.55/4.99  --smt_ac_axioms                         fast
% 35.55/4.99  --preprocessed_out                      false
% 35.55/4.99  --preprocessed_stats                    false
% 35.55/4.99  
% 35.55/4.99  ------ Abstraction refinement Options
% 35.55/4.99  
% 35.55/4.99  --abstr_ref                             []
% 35.55/4.99  --abstr_ref_prep                        false
% 35.55/4.99  --abstr_ref_until_sat                   false
% 35.55/4.99  --abstr_ref_sig_restrict                funpre
% 35.55/4.99  --abstr_ref_af_restrict_to_split_sk     false
% 35.55/4.99  --abstr_ref_under                       []
% 35.55/4.99  
% 35.55/4.99  ------ SAT Options
% 35.55/4.99  
% 35.55/4.99  --sat_mode                              false
% 35.55/4.99  --sat_fm_restart_options                ""
% 35.55/4.99  --sat_gr_def                            false
% 35.55/4.99  --sat_epr_types                         true
% 35.55/4.99  --sat_non_cyclic_types                  false
% 35.55/4.99  --sat_finite_models                     false
% 35.55/4.99  --sat_fm_lemmas                         false
% 35.55/4.99  --sat_fm_prep                           false
% 35.55/4.99  --sat_fm_uc_incr                        true
% 35.55/4.99  --sat_out_model                         small
% 35.55/4.99  --sat_out_clauses                       false
% 35.55/4.99  
% 35.55/4.99  ------ QBF Options
% 35.55/4.99  
% 35.55/4.99  --qbf_mode                              false
% 35.55/4.99  --qbf_elim_univ                         false
% 35.55/4.99  --qbf_dom_inst                          none
% 35.55/4.99  --qbf_dom_pre_inst                      false
% 35.55/4.99  --qbf_sk_in                             false
% 35.55/4.99  --qbf_pred_elim                         true
% 35.55/4.99  --qbf_split                             512
% 35.55/4.99  
% 35.55/4.99  ------ BMC1 Options
% 35.55/4.99  
% 35.55/4.99  --bmc1_incremental                      false
% 35.55/4.99  --bmc1_axioms                           reachable_all
% 35.55/4.99  --bmc1_min_bound                        0
% 35.55/4.99  --bmc1_max_bound                        -1
% 35.55/4.99  --bmc1_max_bound_default                -1
% 35.55/4.99  --bmc1_symbol_reachability              true
% 35.55/4.99  --bmc1_property_lemmas                  false
% 35.55/4.99  --bmc1_k_induction                      false
% 35.55/4.99  --bmc1_non_equiv_states                 false
% 35.55/4.99  --bmc1_deadlock                         false
% 35.55/4.99  --bmc1_ucm                              false
% 35.55/4.99  --bmc1_add_unsat_core                   none
% 35.55/4.99  --bmc1_unsat_core_children              false
% 35.55/4.99  --bmc1_unsat_core_extrapolate_axioms    false
% 35.55/4.99  --bmc1_out_stat                         full
% 35.55/4.99  --bmc1_ground_init                      false
% 35.55/4.99  --bmc1_pre_inst_next_state              false
% 35.55/4.99  --bmc1_pre_inst_state                   false
% 35.55/4.99  --bmc1_pre_inst_reach_state             false
% 35.55/4.99  --bmc1_out_unsat_core                   false
% 35.55/4.99  --bmc1_aig_witness_out                  false
% 35.55/4.99  --bmc1_verbose                          false
% 35.55/4.99  --bmc1_dump_clauses_tptp                false
% 35.55/4.99  --bmc1_dump_unsat_core_tptp             false
% 35.55/4.99  --bmc1_dump_file                        -
% 35.55/4.99  --bmc1_ucm_expand_uc_limit              128
% 35.55/4.99  --bmc1_ucm_n_expand_iterations          6
% 35.55/4.99  --bmc1_ucm_extend_mode                  1
% 35.55/4.99  --bmc1_ucm_init_mode                    2
% 35.55/4.99  --bmc1_ucm_cone_mode                    none
% 35.55/4.99  --bmc1_ucm_reduced_relation_type        0
% 35.55/4.99  --bmc1_ucm_relax_model                  4
% 35.55/4.99  --bmc1_ucm_full_tr_after_sat            true
% 35.55/4.99  --bmc1_ucm_expand_neg_assumptions       false
% 35.55/4.99  --bmc1_ucm_layered_model                none
% 35.55/4.99  --bmc1_ucm_max_lemma_size               10
% 35.55/4.99  
% 35.55/4.99  ------ AIG Options
% 35.55/4.99  
% 35.55/4.99  --aig_mode                              false
% 35.55/4.99  
% 35.55/4.99  ------ Instantiation Options
% 35.55/4.99  
% 35.55/4.99  --instantiation_flag                    true
% 35.55/4.99  --inst_sos_flag                         true
% 35.55/4.99  --inst_sos_phase                        true
% 35.55/4.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.55/4.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.55/4.99  --inst_lit_sel_side                     num_symb
% 35.55/4.99  --inst_solver_per_active                1400
% 35.55/4.99  --inst_solver_calls_frac                1.
% 35.55/4.99  --inst_passive_queue_type               priority_queues
% 35.55/4.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.55/4.99  --inst_passive_queues_freq              [25;2]
% 35.55/4.99  --inst_dismatching                      true
% 35.55/4.99  --inst_eager_unprocessed_to_passive     true
% 35.55/4.99  --inst_prop_sim_given                   true
% 35.55/4.99  --inst_prop_sim_new                     false
% 35.55/4.99  --inst_subs_new                         false
% 35.55/4.99  --inst_eq_res_simp                      false
% 35.55/4.99  --inst_subs_given                       false
% 35.55/4.99  --inst_orphan_elimination               true
% 35.55/4.99  --inst_learning_loop_flag               true
% 35.55/4.99  --inst_learning_start                   3000
% 35.55/4.99  --inst_learning_factor                  2
% 35.55/4.99  --inst_start_prop_sim_after_learn       3
% 35.55/4.99  --inst_sel_renew                        solver
% 35.55/4.99  --inst_lit_activity_flag                true
% 35.55/4.99  --inst_restr_to_given                   false
% 35.55/4.99  --inst_activity_threshold               500
% 35.55/4.99  --inst_out_proof                        true
% 35.55/4.99  
% 35.55/4.99  ------ Resolution Options
% 35.55/4.99  
% 35.55/4.99  --resolution_flag                       true
% 35.55/4.99  --res_lit_sel                           adaptive
% 35.55/4.99  --res_lit_sel_side                      none
% 35.55/4.99  --res_ordering                          kbo
% 35.55/4.99  --res_to_prop_solver                    active
% 35.55/4.99  --res_prop_simpl_new                    false
% 35.55/4.99  --res_prop_simpl_given                  true
% 35.55/4.99  --res_passive_queue_type                priority_queues
% 35.55/4.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.55/4.99  --res_passive_queues_freq               [15;5]
% 35.55/4.99  --res_forward_subs                      full
% 35.55/4.99  --res_backward_subs                     full
% 35.55/4.99  --res_forward_subs_resolution           true
% 35.55/4.99  --res_backward_subs_resolution          true
% 35.55/4.99  --res_orphan_elimination                true
% 35.55/4.99  --res_time_limit                        2.
% 35.55/4.99  --res_out_proof                         true
% 35.55/4.99  
% 35.55/4.99  ------ Superposition Options
% 35.55/4.99  
% 35.55/4.99  --superposition_flag                    true
% 35.55/4.99  --sup_passive_queue_type                priority_queues
% 35.55/4.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.55/4.99  --sup_passive_queues_freq               [8;1;4]
% 35.55/4.99  --demod_completeness_check              fast
% 35.55/4.99  --demod_use_ground                      true
% 35.55/4.99  --sup_to_prop_solver                    passive
% 35.55/4.99  --sup_prop_simpl_new                    true
% 35.55/4.99  --sup_prop_simpl_given                  true
% 35.55/4.99  --sup_fun_splitting                     true
% 35.55/4.99  --sup_smt_interval                      50000
% 35.55/4.99  
% 35.55/4.99  ------ Superposition Simplification Setup
% 35.55/4.99  
% 35.55/4.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.55/4.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.55/4.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.55/4.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.55/4.99  --sup_full_triv                         [TrivRules;PropSubs]
% 35.55/4.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.55/4.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.55/4.99  --sup_immed_triv                        [TrivRules]
% 35.55/4.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.55/4.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.55/4.99  --sup_immed_bw_main                     []
% 35.55/4.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.55/4.99  --sup_input_triv                        [Unflattening;TrivRules]
% 35.55/4.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.55/4.99  --sup_input_bw                          []
% 35.55/4.99  
% 35.55/4.99  ------ Combination Options
% 35.55/4.99  
% 35.55/4.99  --comb_res_mult                         3
% 35.55/4.99  --comb_sup_mult                         2
% 35.55/4.99  --comb_inst_mult                        10
% 35.55/4.99  
% 35.55/4.99  ------ Debug Options
% 35.55/4.99  
% 35.55/4.99  --dbg_backtrace                         false
% 35.55/4.99  --dbg_dump_prop_clauses                 false
% 35.55/4.99  --dbg_dump_prop_clauses_file            -
% 35.55/4.99  --dbg_out_stat                          false
% 35.55/4.99  ------ Parsing...
% 35.55/4.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.55/4.99  
% 35.55/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 35.55/4.99  
% 35.55/4.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.55/4.99  
% 35.55/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.55/4.99  ------ Proving...
% 35.55/4.99  ------ Problem Properties 
% 35.55/4.99  
% 35.55/4.99  
% 35.55/4.99  clauses                                 12
% 35.55/4.99  conjectures                             6
% 35.55/4.99  EPR                                     1
% 35.55/4.99  Horn                                    12
% 35.55/4.99  unary                                   6
% 35.55/4.99  binary                                  0
% 35.55/4.99  lits                                    25
% 35.55/4.99  lits eq                                 8
% 35.55/4.99  fd_pure                                 0
% 35.55/4.99  fd_pseudo                               0
% 35.55/4.99  fd_cond                                 0
% 35.55/4.99  fd_pseudo_cond                          0
% 35.55/4.99  AC symbols                              0
% 35.55/4.99  
% 35.55/4.99  ------ Schedule dynamic 5 is on 
% 35.55/4.99  
% 35.55/4.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.55/4.99  
% 35.55/4.99  
% 35.55/4.99  ------ 
% 35.55/4.99  Current options:
% 35.55/4.99  ------ 
% 35.55/4.99  
% 35.55/4.99  ------ Input Options
% 35.55/4.99  
% 35.55/4.99  --out_options                           all
% 35.55/4.99  --tptp_safe_out                         true
% 35.55/4.99  --problem_path                          ""
% 35.55/4.99  --include_path                          ""
% 35.55/4.99  --clausifier                            res/vclausify_rel
% 35.55/4.99  --clausifier_options                    ""
% 35.55/4.99  --stdin                                 false
% 35.55/4.99  --stats_out                             all
% 35.55/4.99  
% 35.55/4.99  ------ General Options
% 35.55/4.99  
% 35.55/4.99  --fof                                   false
% 35.55/4.99  --time_out_real                         305.
% 35.55/4.99  --time_out_virtual                      -1.
% 35.55/4.99  --symbol_type_check                     false
% 35.55/4.99  --clausify_out                          false
% 35.55/4.99  --sig_cnt_out                           false
% 35.55/4.99  --trig_cnt_out                          false
% 35.55/4.99  --trig_cnt_out_tolerance                1.
% 35.55/4.99  --trig_cnt_out_sk_spl                   false
% 35.55/4.99  --abstr_cl_out                          false
% 35.55/4.99  
% 35.55/4.99  ------ Global Options
% 35.55/4.99  
% 35.55/4.99  --schedule                              default
% 35.55/4.99  --add_important_lit                     false
% 35.55/4.99  --prop_solver_per_cl                    1000
% 35.55/4.99  --min_unsat_core                        false
% 35.55/4.99  --soft_assumptions                      false
% 35.55/4.99  --soft_lemma_size                       3
% 35.55/4.99  --prop_impl_unit_size                   0
% 35.55/4.99  --prop_impl_unit                        []
% 35.55/4.99  --share_sel_clauses                     true
% 35.55/4.99  --reset_solvers                         false
% 35.55/4.99  --bc_imp_inh                            [conj_cone]
% 35.55/4.99  --conj_cone_tolerance                   3.
% 35.55/4.99  --extra_neg_conj                        none
% 35.55/4.99  --large_theory_mode                     true
% 35.55/4.99  --prolific_symb_bound                   200
% 35.55/4.99  --lt_threshold                          2000
% 35.55/4.99  --clause_weak_htbl                      true
% 35.55/4.99  --gc_record_bc_elim                     false
% 35.55/4.99  
% 35.55/4.99  ------ Preprocessing Options
% 35.55/4.99  
% 35.55/4.99  --preprocessing_flag                    true
% 35.55/4.99  --time_out_prep_mult                    0.1
% 35.55/4.99  --splitting_mode                        input
% 35.55/4.99  --splitting_grd                         true
% 35.55/4.99  --splitting_cvd                         false
% 35.55/4.99  --splitting_cvd_svl                     false
% 35.55/4.99  --splitting_nvd                         32
% 35.55/4.99  --sub_typing                            true
% 35.55/4.99  --prep_gs_sim                           true
% 35.55/4.99  --prep_unflatten                        true
% 35.55/4.99  --prep_res_sim                          true
% 35.55/4.99  --prep_upred                            true
% 35.55/4.99  --prep_sem_filter                       exhaustive
% 35.55/4.99  --prep_sem_filter_out                   false
% 35.55/4.99  --pred_elim                             true
% 35.55/4.99  --res_sim_input                         true
% 35.55/4.99  --eq_ax_congr_red                       true
% 35.55/4.99  --pure_diseq_elim                       true
% 35.55/4.99  --brand_transform                       false
% 35.55/4.99  --non_eq_to_eq                          false
% 35.55/4.99  --prep_def_merge                        true
% 35.55/4.99  --prep_def_merge_prop_impl              false
% 35.55/4.99  --prep_def_merge_mbd                    true
% 35.55/4.99  --prep_def_merge_tr_red                 false
% 35.55/4.99  --prep_def_merge_tr_cl                  false
% 35.55/4.99  --smt_preprocessing                     true
% 35.55/4.99  --smt_ac_axioms                         fast
% 35.55/4.99  --preprocessed_out                      false
% 35.55/4.99  --preprocessed_stats                    false
% 35.55/4.99  
% 35.55/4.99  ------ Abstraction refinement Options
% 35.55/4.99  
% 35.55/4.99  --abstr_ref                             []
% 35.55/4.99  --abstr_ref_prep                        false
% 35.55/4.99  --abstr_ref_until_sat                   false
% 35.55/4.99  --abstr_ref_sig_restrict                funpre
% 35.55/4.99  --abstr_ref_af_restrict_to_split_sk     false
% 35.55/4.99  --abstr_ref_under                       []
% 35.55/4.99  
% 35.55/4.99  ------ SAT Options
% 35.55/4.99  
% 35.55/4.99  --sat_mode                              false
% 35.55/4.99  --sat_fm_restart_options                ""
% 35.55/4.99  --sat_gr_def                            false
% 35.55/4.99  --sat_epr_types                         true
% 35.55/4.99  --sat_non_cyclic_types                  false
% 35.55/4.99  --sat_finite_models                     false
% 35.55/4.99  --sat_fm_lemmas                         false
% 35.55/4.99  --sat_fm_prep                           false
% 35.55/4.99  --sat_fm_uc_incr                        true
% 35.55/4.99  --sat_out_model                         small
% 35.55/4.99  --sat_out_clauses                       false
% 35.55/4.99  
% 35.55/4.99  ------ QBF Options
% 35.55/4.99  
% 35.55/4.99  --qbf_mode                              false
% 35.55/4.99  --qbf_elim_univ                         false
% 35.55/4.99  --qbf_dom_inst                          none
% 35.55/4.99  --qbf_dom_pre_inst                      false
% 35.55/4.99  --qbf_sk_in                             false
% 35.55/4.99  --qbf_pred_elim                         true
% 35.55/4.99  --qbf_split                             512
% 35.55/4.99  
% 35.55/4.99  ------ BMC1 Options
% 35.55/4.99  
% 35.55/4.99  --bmc1_incremental                      false
% 35.55/4.99  --bmc1_axioms                           reachable_all
% 35.55/4.99  --bmc1_min_bound                        0
% 35.55/4.99  --bmc1_max_bound                        -1
% 35.55/4.99  --bmc1_max_bound_default                -1
% 35.55/4.99  --bmc1_symbol_reachability              true
% 35.55/4.99  --bmc1_property_lemmas                  false
% 35.55/4.99  --bmc1_k_induction                      false
% 35.55/4.99  --bmc1_non_equiv_states                 false
% 35.55/4.99  --bmc1_deadlock                         false
% 35.55/4.99  --bmc1_ucm                              false
% 35.55/4.99  --bmc1_add_unsat_core                   none
% 35.55/4.99  --bmc1_unsat_core_children              false
% 35.55/4.99  --bmc1_unsat_core_extrapolate_axioms    false
% 35.55/4.99  --bmc1_out_stat                         full
% 35.55/4.99  --bmc1_ground_init                      false
% 35.55/4.99  --bmc1_pre_inst_next_state              false
% 35.55/4.99  --bmc1_pre_inst_state                   false
% 35.55/4.99  --bmc1_pre_inst_reach_state             false
% 35.55/4.99  --bmc1_out_unsat_core                   false
% 35.55/4.99  --bmc1_aig_witness_out                  false
% 35.55/4.99  --bmc1_verbose                          false
% 35.55/4.99  --bmc1_dump_clauses_tptp                false
% 35.55/4.99  --bmc1_dump_unsat_core_tptp             false
% 35.55/4.99  --bmc1_dump_file                        -
% 35.55/4.99  --bmc1_ucm_expand_uc_limit              128
% 35.55/4.99  --bmc1_ucm_n_expand_iterations          6
% 35.55/4.99  --bmc1_ucm_extend_mode                  1
% 35.55/4.99  --bmc1_ucm_init_mode                    2
% 35.55/4.99  --bmc1_ucm_cone_mode                    none
% 35.55/4.99  --bmc1_ucm_reduced_relation_type        0
% 35.55/4.99  --bmc1_ucm_relax_model                  4
% 35.55/4.99  --bmc1_ucm_full_tr_after_sat            true
% 35.55/4.99  --bmc1_ucm_expand_neg_assumptions       false
% 35.55/4.99  --bmc1_ucm_layered_model                none
% 35.55/4.99  --bmc1_ucm_max_lemma_size               10
% 35.55/4.99  
% 35.55/4.99  ------ AIG Options
% 35.55/4.99  
% 35.55/4.99  --aig_mode                              false
% 35.55/4.99  
% 35.55/4.99  ------ Instantiation Options
% 35.55/4.99  
% 35.55/4.99  --instantiation_flag                    true
% 35.55/4.99  --inst_sos_flag                         true
% 35.55/4.99  --inst_sos_phase                        true
% 35.55/4.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.55/4.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.55/4.99  --inst_lit_sel_side                     none
% 35.55/4.99  --inst_solver_per_active                1400
% 35.55/4.99  --inst_solver_calls_frac                1.
% 35.55/4.99  --inst_passive_queue_type               priority_queues
% 35.55/4.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.55/4.99  --inst_passive_queues_freq              [25;2]
% 35.55/4.99  --inst_dismatching                      true
% 35.55/4.99  --inst_eager_unprocessed_to_passive     true
% 35.55/4.99  --inst_prop_sim_given                   true
% 35.55/4.99  --inst_prop_sim_new                     false
% 35.55/4.99  --inst_subs_new                         false
% 35.55/4.99  --inst_eq_res_simp                      false
% 35.55/4.99  --inst_subs_given                       false
% 35.55/4.99  --inst_orphan_elimination               true
% 35.55/4.99  --inst_learning_loop_flag               true
% 35.55/4.99  --inst_learning_start                   3000
% 35.55/4.99  --inst_learning_factor                  2
% 35.55/4.99  --inst_start_prop_sim_after_learn       3
% 35.55/4.99  --inst_sel_renew                        solver
% 35.55/4.99  --inst_lit_activity_flag                true
% 35.55/4.99  --inst_restr_to_given                   false
% 35.55/4.99  --inst_activity_threshold               500
% 35.55/4.99  --inst_out_proof                        true
% 35.55/4.99  
% 35.55/4.99  ------ Resolution Options
% 35.55/4.99  
% 35.55/4.99  --resolution_flag                       false
% 35.55/4.99  --res_lit_sel                           adaptive
% 35.55/4.99  --res_lit_sel_side                      none
% 35.55/4.99  --res_ordering                          kbo
% 35.55/4.99  --res_to_prop_solver                    active
% 35.55/4.99  --res_prop_simpl_new                    false
% 35.55/4.99  --res_prop_simpl_given                  true
% 35.55/4.99  --res_passive_queue_type                priority_queues
% 35.55/4.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.55/4.99  --res_passive_queues_freq               [15;5]
% 35.55/4.99  --res_forward_subs                      full
% 35.55/4.99  --res_backward_subs                     full
% 35.55/4.99  --res_forward_subs_resolution           true
% 35.55/4.99  --res_backward_subs_resolution          true
% 35.55/4.99  --res_orphan_elimination                true
% 35.55/4.99  --res_time_limit                        2.
% 35.55/4.99  --res_out_proof                         true
% 35.55/4.99  
% 35.55/4.99  ------ Superposition Options
% 35.55/4.99  
% 35.55/4.99  --superposition_flag                    true
% 35.55/4.99  --sup_passive_queue_type                priority_queues
% 35.55/4.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.55/4.99  --sup_passive_queues_freq               [8;1;4]
% 35.55/4.99  --demod_completeness_check              fast
% 35.55/4.99  --demod_use_ground                      true
% 35.55/4.99  --sup_to_prop_solver                    passive
% 35.55/4.99  --sup_prop_simpl_new                    true
% 35.55/4.99  --sup_prop_simpl_given                  true
% 35.55/4.99  --sup_fun_splitting                     true
% 35.55/4.99  --sup_smt_interval                      50000
% 35.55/4.99  
% 35.55/4.99  ------ Superposition Simplification Setup
% 35.55/4.99  
% 35.55/4.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.55/4.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.55/4.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.55/4.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.55/4.99  --sup_full_triv                         [TrivRules;PropSubs]
% 35.55/4.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.55/4.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.55/4.99  --sup_immed_triv                        [TrivRules]
% 35.55/4.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.55/4.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.55/4.99  --sup_immed_bw_main                     []
% 35.55/4.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.55/4.99  --sup_input_triv                        [Unflattening;TrivRules]
% 35.55/4.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.55/4.99  --sup_input_bw                          []
% 35.55/4.99  
% 35.55/4.99  ------ Combination Options
% 35.55/4.99  
% 35.55/4.99  --comb_res_mult                         3
% 35.55/4.99  --comb_sup_mult                         2
% 35.55/4.99  --comb_inst_mult                        10
% 35.55/4.99  
% 35.55/4.99  ------ Debug Options
% 35.55/4.99  
% 35.55/4.99  --dbg_backtrace                         false
% 35.55/4.99  --dbg_dump_prop_clauses                 false
% 35.55/4.99  --dbg_dump_prop_clauses_file            -
% 35.55/4.99  --dbg_out_stat                          false
% 35.55/4.99  
% 35.55/4.99  
% 35.55/4.99  
% 35.55/4.99  
% 35.55/4.99  ------ Proving...
% 35.55/4.99  
% 35.55/4.99  
% 35.55/4.99  % SZS status Theorem for theBenchmark.p
% 35.55/4.99  
% 35.55/4.99  % SZS output start CNFRefutation for theBenchmark.p
% 35.55/4.99  
% 35.55/4.99  fof(f9,conjecture,(
% 35.55/4.99    ! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 35.55/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.55/4.99  
% 35.55/4.99  fof(f10,negated_conjecture,(
% 35.55/4.99    ~! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 35.55/4.99    inference(negated_conjecture,[],[f9])).
% 35.55/4.99  
% 35.55/4.99  fof(f29,plain,(
% 35.55/4.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((X2 != X3 & (k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 35.55/4.99    inference(ennf_transformation,[],[f10])).
% 35.55/4.99  
% 35.55/4.99  fof(f30,plain,(
% 35.55/4.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 35.55/4.99    inference(flattening,[],[f29])).
% 35.55/4.99  
% 35.55/4.99  fof(f39,plain,(
% 35.55/4.99    ( ! [X2,X0,X1] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (sK5 != X2 & k3_lattices(X0,X1,sK5) = k3_lattices(X0,X1,X2) & k4_lattices(X0,X1,sK5) = k4_lattices(X0,X1,X2) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 35.55/4.99    introduced(choice_axiom,[])).
% 35.55/4.99  
% 35.55/4.99  fof(f38,plain,(
% 35.55/4.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (sK4 != X3 & k3_lattices(X0,X1,sK4) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,sK4) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 35.55/4.99    introduced(choice_axiom,[])).
% 35.55/4.99  
% 35.55/4.99  fof(f37,plain,(
% 35.55/4.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,sK3,X2) = k3_lattices(X0,sK3,X3) & k4_lattices(X0,sK3,X2) = k4_lattices(X0,sK3,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 35.55/4.99    introduced(choice_axiom,[])).
% 35.55/4.99  
% 35.55/4.99  fof(f36,plain,(
% 35.55/4.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(sK2,X1,X2) = k3_lattices(sK2,X1,X3) & k4_lattices(sK2,X1,X2) = k4_lattices(sK2,X1,X3) & m1_subset_1(X3,u1_struct_0(sK2))) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l3_lattices(sK2) & v11_lattices(sK2) & v10_lattices(sK2) & ~v2_struct_0(sK2))),
% 35.55/4.99    introduced(choice_axiom,[])).
% 35.55/4.99  
% 35.55/4.99  fof(f40,plain,(
% 35.55/4.99    (((sK4 != sK5 & k3_lattices(sK2,sK3,sK4) = k3_lattices(sK2,sK3,sK5) & k4_lattices(sK2,sK3,sK4) = k4_lattices(sK2,sK3,sK5) & m1_subset_1(sK5,u1_struct_0(sK2))) & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l3_lattices(sK2) & v11_lattices(sK2) & v10_lattices(sK2) & ~v2_struct_0(sK2)),
% 35.55/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f30,f39,f38,f37,f36])).
% 35.55/4.99  
% 35.55/4.99  fof(f61,plain,(
% 35.55/4.99    m1_subset_1(sK4,u1_struct_0(sK2))),
% 35.55/4.99    inference(cnf_transformation,[],[f40])).
% 35.55/4.99  
% 35.55/4.99  fof(f63,plain,(
% 35.55/4.99    k4_lattices(sK2,sK3,sK4) = k4_lattices(sK2,sK3,sK5)),
% 35.55/4.99    inference(cnf_transformation,[],[f40])).
% 35.55/4.99  
% 35.55/4.99  fof(f4,axiom,(
% 35.55/4.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 35.55/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.55/4.99  
% 35.55/4.99  fof(f20,plain,(
% 35.55/4.99    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 35.55/4.99    inference(ennf_transformation,[],[f4])).
% 35.55/4.99  
% 35.55/4.99  fof(f21,plain,(
% 35.55/4.99    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 35.55/4.99    inference(flattening,[],[f20])).
% 35.55/4.99  
% 35.55/4.99  fof(f50,plain,(
% 35.55/4.99    ( ! [X2,X0,X1] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 35.55/4.99    inference(cnf_transformation,[],[f21])).
% 35.55/4.99  
% 35.55/4.99  fof(f1,axiom,(
% 35.55/4.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 35.55/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.55/4.99  
% 35.55/4.99  fof(f11,plain,(
% 35.55/4.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 35.55/4.99    inference(pure_predicate_removal,[],[f1])).
% 35.55/4.99  
% 35.55/4.99  fof(f12,plain,(
% 35.55/4.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 35.55/4.99    inference(pure_predicate_removal,[],[f11])).
% 35.55/4.99  
% 35.55/4.99  fof(f13,plain,(
% 35.55/4.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 35.55/4.99    inference(pure_predicate_removal,[],[f12])).
% 35.55/4.99  
% 35.55/4.99  fof(f14,plain,(
% 35.55/4.99    ! [X0] : (((v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 35.55/4.99    inference(ennf_transformation,[],[f13])).
% 35.55/4.99  
% 35.55/4.99  fof(f15,plain,(
% 35.55/4.99    ! [X0] : ((v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 35.55/4.99    inference(flattening,[],[f14])).
% 35.55/4.99  
% 35.55/4.99  fof(f43,plain,(
% 35.55/4.99    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 35.55/4.99    inference(cnf_transformation,[],[f15])).
% 35.55/4.99  
% 35.55/4.99  fof(f57,plain,(
% 35.55/4.99    v10_lattices(sK2)),
% 35.55/4.99    inference(cnf_transformation,[],[f40])).
% 35.55/4.99  
% 35.55/4.99  fof(f56,plain,(
% 35.55/4.99    ~v2_struct_0(sK2)),
% 35.55/4.99    inference(cnf_transformation,[],[f40])).
% 35.55/4.99  
% 35.55/4.99  fof(f59,plain,(
% 35.55/4.99    l3_lattices(sK2)),
% 35.55/4.99    inference(cnf_transformation,[],[f40])).
% 35.55/4.99  
% 35.55/4.99  fof(f5,axiom,(
% 35.55/4.99    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 35.55/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.55/4.99  
% 35.55/4.99  fof(f22,plain,(
% 35.55/4.99    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 35.55/4.99    inference(ennf_transformation,[],[f5])).
% 35.55/4.99  
% 35.55/4.99  fof(f51,plain,(
% 35.55/4.99    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 35.55/4.99    inference(cnf_transformation,[],[f22])).
% 35.55/4.99  
% 35.55/4.99  fof(f60,plain,(
% 35.55/4.99    m1_subset_1(sK3,u1_struct_0(sK2))),
% 35.55/4.99    inference(cnf_transformation,[],[f40])).
% 35.55/4.99  
% 35.55/4.99  fof(f7,axiom,(
% 35.55/4.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2))),
% 35.55/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.55/4.99  
% 35.55/4.99  fof(f25,plain,(
% 35.55/4.99    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 35.55/4.99    inference(ennf_transformation,[],[f7])).
% 35.55/4.99  
% 35.55/4.99  fof(f26,plain,(
% 35.55/4.99    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 35.55/4.99    inference(flattening,[],[f25])).
% 35.55/4.99  
% 35.55/4.99  fof(f54,plain,(
% 35.55/4.99    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 35.55/4.99    inference(cnf_transformation,[],[f26])).
% 35.55/4.99  
% 35.55/4.99  fof(f62,plain,(
% 35.55/4.99    m1_subset_1(sK5,u1_struct_0(sK2))),
% 35.55/4.99    inference(cnf_transformation,[],[f40])).
% 35.55/4.99  
% 35.55/4.99  fof(f6,axiom,(
% 35.55/4.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 35.55/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.55/4.99  
% 35.55/4.99  fof(f23,plain,(
% 35.55/4.99    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 35.55/4.99    inference(ennf_transformation,[],[f6])).
% 35.55/4.99  
% 35.55/4.99  fof(f24,plain,(
% 35.55/4.99    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 35.55/4.99    inference(flattening,[],[f23])).
% 35.55/4.99  
% 35.55/4.99  fof(f53,plain,(
% 35.55/4.99    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 35.55/4.99    inference(cnf_transformation,[],[f24])).
% 35.55/4.99  
% 35.55/4.99  fof(f42,plain,(
% 35.55/4.99    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 35.55/4.99    inference(cnf_transformation,[],[f15])).
% 35.55/4.99  
% 35.55/4.99  fof(f52,plain,(
% 35.55/4.99    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 35.55/4.99    inference(cnf_transformation,[],[f22])).
% 35.55/4.99  
% 35.55/4.99  fof(f3,axiom,(
% 35.55/4.99    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 35.55/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.55/4.99  
% 35.55/4.99  fof(f18,plain,(
% 35.55/4.99    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 35.55/4.99    inference(ennf_transformation,[],[f3])).
% 35.55/4.99  
% 35.55/4.99  fof(f19,plain,(
% 35.55/4.99    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 35.55/4.99    inference(flattening,[],[f18])).
% 35.55/4.99  
% 35.55/4.99  fof(f31,plain,(
% 35.55/4.99    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 35.55/4.99    inference(nnf_transformation,[],[f19])).
% 35.55/4.99  
% 35.55/4.99  fof(f32,plain,(
% 35.55/4.99    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 35.55/4.99    inference(rectify,[],[f31])).
% 35.55/4.99  
% 35.55/4.99  fof(f34,plain,(
% 35.55/4.99    ( ! [X1] : (! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (k1_lattices(X0,k2_lattices(X0,X1,sK1(X0)),sK1(X0)) != sK1(X0) & m1_subset_1(sK1(X0),u1_struct_0(X0))))) )),
% 35.55/4.99    introduced(choice_axiom,[])).
% 35.55/4.99  
% 35.55/4.99  fof(f33,plain,(
% 35.55/4.99    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK0(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0))))),
% 35.55/4.99    introduced(choice_axiom,[])).
% 35.55/4.99  
% 35.55/4.99  fof(f35,plain,(
% 35.55/4.99    ! [X0] : (((v8_lattices(X0) | ((k1_lattices(X0,k2_lattices(X0,sK0(X0),sK1(X0)),sK1(X0)) != sK1(X0) & m1_subset_1(sK1(X0),u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 35.55/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 35.55/4.99  
% 35.55/4.99  fof(f46,plain,(
% 35.55/4.99    ( ! [X4,X0,X3] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v8_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 35.55/4.99    inference(cnf_transformation,[],[f35])).
% 35.55/4.99  
% 35.55/4.99  fof(f44,plain,(
% 35.55/4.99    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 35.55/4.99    inference(cnf_transformation,[],[f15])).
% 35.55/4.99  
% 35.55/4.99  fof(f2,axiom,(
% 35.55/4.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 35.55/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.55/4.99  
% 35.55/4.99  fof(f16,plain,(
% 35.55/4.99    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 35.55/4.99    inference(ennf_transformation,[],[f2])).
% 35.55/4.99  
% 35.55/4.99  fof(f17,plain,(
% 35.55/4.99    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 35.55/4.99    inference(flattening,[],[f16])).
% 35.55/4.99  
% 35.55/4.99  fof(f45,plain,(
% 35.55/4.99    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 35.55/4.99    inference(cnf_transformation,[],[f17])).
% 35.55/4.99  
% 35.55/4.99  fof(f8,axiom,(
% 35.55/4.99    ! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))))))),
% 35.55/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.55/4.99  
% 35.55/4.99  fof(f27,plain,(
% 35.55/4.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 35.55/4.99    inference(ennf_transformation,[],[f8])).
% 35.55/4.99  
% 35.55/4.99  fof(f28,plain,(
% 35.55/4.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 35.55/4.99    inference(flattening,[],[f27])).
% 35.55/4.99  
% 35.55/4.99  fof(f55,plain,(
% 35.55/4.99    ( ! [X2,X0,X3,X1] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 35.55/4.99    inference(cnf_transformation,[],[f28])).
% 35.55/4.99  
% 35.55/4.99  fof(f58,plain,(
% 35.55/4.99    v11_lattices(sK2)),
% 35.55/4.99    inference(cnf_transformation,[],[f40])).
% 35.55/4.99  
% 35.55/4.99  fof(f64,plain,(
% 35.55/4.99    k3_lattices(sK2,sK3,sK4) = k3_lattices(sK2,sK3,sK5)),
% 35.55/4.99    inference(cnf_transformation,[],[f40])).
% 35.55/4.99  
% 35.55/4.99  fof(f65,plain,(
% 35.55/4.99    sK4 != sK5),
% 35.55/4.99    inference(cnf_transformation,[],[f40])).
% 35.55/4.99  
% 35.55/4.99  cnf(c_515,plain,
% 35.55/4.99      ( X0_49 != X1_49 | X2_49 != X1_49 | X2_49 = X0_49 ),
% 35.55/4.99      theory(equality) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_82503,plain,
% 35.55/4.99      ( X0_49 != X1_49 | sK4 != X1_49 | sK4 = X0_49 ),
% 35.55/4.99      inference(instantiation,[status(thm)],[c_515]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_82681,plain,
% 35.55/4.99      ( X0_49 != sK4 | sK4 = X0_49 | sK4 != sK4 ),
% 35.55/4.99      inference(instantiation,[status(thm)],[c_82503]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_127738,plain,
% 35.55/4.99      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 35.55/4.99      inference(instantiation,[status(thm)],[c_82681]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_19,negated_conjecture,
% 35.55/4.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 35.55/4.99      inference(cnf_transformation,[],[f61]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_508,negated_conjecture,
% 35.55/4.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 35.55/4.99      inference(subtyping,[status(esa)],[c_19]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_677,plain,
% 35.55/4.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 35.55/4.99      inference(predicate_to_equality,[status(thm)],[c_508]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_17,negated_conjecture,
% 35.55/4.99      ( k4_lattices(sK2,sK3,sK4) = k4_lattices(sK2,sK3,sK5) ),
% 35.55/4.99      inference(cnf_transformation,[],[f63]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_510,negated_conjecture,
% 35.55/4.99      ( k4_lattices(sK2,sK3,sK4) = k4_lattices(sK2,sK3,sK5) ),
% 35.55/4.99      inference(subtyping,[status(esa)],[c_17]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_9,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 35.55/4.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 35.55/4.99      | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
% 35.55/4.99      | ~ l1_lattices(X1)
% 35.55/4.99      | ~ v6_lattices(X1)
% 35.55/4.99      | v2_struct_0(X1) ),
% 35.55/4.99      inference(cnf_transformation,[],[f50]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_1,plain,
% 35.55/4.99      ( v6_lattices(X0)
% 35.55/4.99      | ~ l3_lattices(X0)
% 35.55/4.99      | v2_struct_0(X0)
% 35.55/4.99      | ~ v10_lattices(X0) ),
% 35.55/4.99      inference(cnf_transformation,[],[f43]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_23,negated_conjecture,
% 35.55/4.99      ( v10_lattices(sK2) ),
% 35.55/4.99      inference(cnf_transformation,[],[f57]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_279,plain,
% 35.55/4.99      ( v6_lattices(X0)
% 35.55/4.99      | ~ l3_lattices(X0)
% 35.55/4.99      | v2_struct_0(X0)
% 35.55/4.99      | sK2 != X0 ),
% 35.55/4.99      inference(resolution_lifted,[status(thm)],[c_1,c_23]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_280,plain,
% 35.55/4.99      ( v6_lattices(sK2) | ~ l3_lattices(sK2) | v2_struct_0(sK2) ),
% 35.55/4.99      inference(unflattening,[status(thm)],[c_279]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_24,negated_conjecture,
% 35.55/4.99      ( ~ v2_struct_0(sK2) ),
% 35.55/4.99      inference(cnf_transformation,[],[f56]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_21,negated_conjecture,
% 35.55/4.99      ( l3_lattices(sK2) ),
% 35.55/4.99      inference(cnf_transformation,[],[f59]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_70,plain,
% 35.55/4.99      ( v6_lattices(sK2)
% 35.55/4.99      | ~ l3_lattices(sK2)
% 35.55/4.99      | v2_struct_0(sK2)
% 35.55/4.99      | ~ v10_lattices(sK2) ),
% 35.55/4.99      inference(instantiation,[status(thm)],[c_1]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_282,plain,
% 35.55/4.99      ( v6_lattices(sK2) ),
% 35.55/4.99      inference(global_propositional_subsumption,
% 35.55/4.99                [status(thm)],
% 35.55/4.99                [c_280,c_24,c_23,c_21,c_70]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_328,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 35.55/4.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 35.55/4.99      | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
% 35.55/4.99      | ~ l1_lattices(X1)
% 35.55/4.99      | v2_struct_0(X1)
% 35.55/4.99      | sK2 != X1 ),
% 35.55/4.99      inference(resolution_lifted,[status(thm)],[c_9,c_282]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_329,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 35.55/4.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 35.55/4.99      | m1_subset_1(k4_lattices(sK2,X0,X1),u1_struct_0(sK2))
% 35.55/4.99      | ~ l1_lattices(sK2)
% 35.55/4.99      | v2_struct_0(sK2) ),
% 35.55/4.99      inference(unflattening,[status(thm)],[c_328]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_11,plain,
% 35.55/4.99      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 35.55/4.99      inference(cnf_transformation,[],[f51]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_42,plain,
% 35.55/4.99      ( l1_lattices(sK2) | ~ l3_lattices(sK2) ),
% 35.55/4.99      inference(instantiation,[status(thm)],[c_11]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_333,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 35.55/4.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 35.55/4.99      | m1_subset_1(k4_lattices(sK2,X0,X1),u1_struct_0(sK2)) ),
% 35.55/4.99      inference(global_propositional_subsumption,
% 35.55/4.99                [status(thm)],
% 35.55/4.99                [c_329,c_24,c_21,c_42]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_504,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
% 35.55/4.99      | ~ m1_subset_1(X1_49,u1_struct_0(sK2))
% 35.55/4.99      | m1_subset_1(k4_lattices(sK2,X0_49,X1_49),u1_struct_0(sK2)) ),
% 35.55/4.99      inference(subtyping,[status(esa)],[c_333]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_681,plain,
% 35.55/4.99      ( m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
% 35.55/4.99      | m1_subset_1(X1_49,u1_struct_0(sK2)) != iProver_top
% 35.55/4.99      | m1_subset_1(k4_lattices(sK2,X0_49,X1_49),u1_struct_0(sK2)) = iProver_top ),
% 35.55/4.99      inference(predicate_to_equality,[status(thm)],[c_504]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_1871,plain,
% 35.55/4.99      ( m1_subset_1(k4_lattices(sK2,sK3,sK4),u1_struct_0(sK2)) = iProver_top
% 35.55/4.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 35.55/4.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 35.55/4.99      inference(superposition,[status(thm)],[c_510,c_681]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_20,negated_conjecture,
% 35.55/4.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 35.55/4.99      inference(cnf_transformation,[],[f60]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_507,negated_conjecture,
% 35.55/4.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 35.55/4.99      inference(subtyping,[status(esa)],[c_20]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_678,plain,
% 35.55/4.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 35.55/4.99      inference(predicate_to_equality,[status(thm)],[c_507]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_13,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 35.55/4.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 35.55/4.99      | ~ l1_lattices(X1)
% 35.55/4.99      | ~ v6_lattices(X1)
% 35.55/4.99      | v2_struct_0(X1)
% 35.55/4.99      | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0) ),
% 35.55/4.99      inference(cnf_transformation,[],[f54]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_307,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 35.55/4.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 35.55/4.99      | ~ l1_lattices(X1)
% 35.55/4.99      | v2_struct_0(X1)
% 35.55/4.99      | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0)
% 35.55/4.99      | sK2 != X1 ),
% 35.55/4.99      inference(resolution_lifted,[status(thm)],[c_13,c_282]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_308,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 35.55/4.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 35.55/4.99      | ~ l1_lattices(sK2)
% 35.55/4.99      | v2_struct_0(sK2)
% 35.55/4.99      | k4_lattices(sK2,X0,X1) = k2_lattices(sK2,X0,X1) ),
% 35.55/4.99      inference(unflattening,[status(thm)],[c_307]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_312,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 35.55/4.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 35.55/4.99      | k4_lattices(sK2,X0,X1) = k2_lattices(sK2,X0,X1) ),
% 35.55/4.99      inference(global_propositional_subsumption,
% 35.55/4.99                [status(thm)],
% 35.55/4.99                [c_308,c_24,c_21,c_42]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_505,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
% 35.55/4.99      | ~ m1_subset_1(X1_49,u1_struct_0(sK2))
% 35.55/4.99      | k4_lattices(sK2,X0_49,X1_49) = k2_lattices(sK2,X0_49,X1_49) ),
% 35.55/4.99      inference(subtyping,[status(esa)],[c_312]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_680,plain,
% 35.55/4.99      ( k4_lattices(sK2,X0_49,X1_49) = k2_lattices(sK2,X0_49,X1_49)
% 35.55/4.99      | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
% 35.55/4.99      | m1_subset_1(X1_49,u1_struct_0(sK2)) != iProver_top ),
% 35.55/4.99      inference(predicate_to_equality,[status(thm)],[c_505]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_1308,plain,
% 35.55/4.99      ( k4_lattices(sK2,sK3,X0_49) = k2_lattices(sK2,sK3,X0_49)
% 35.55/4.99      | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
% 35.55/4.99      inference(superposition,[status(thm)],[c_678,c_680]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_1822,plain,
% 35.55/4.99      ( k4_lattices(sK2,sK3,sK4) = k2_lattices(sK2,sK3,sK4) ),
% 35.55/4.99      inference(superposition,[status(thm)],[c_677,c_1308]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_1891,plain,
% 35.55/4.99      ( m1_subset_1(k2_lattices(sK2,sK3,sK4),u1_struct_0(sK2)) = iProver_top
% 35.55/4.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 35.55/4.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 35.55/4.99      inference(light_normalisation,[status(thm)],[c_1871,c_1822]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_29,plain,
% 35.55/4.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 35.55/4.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_18,negated_conjecture,
% 35.55/4.99      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 35.55/4.99      inference(cnf_transformation,[],[f62]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_31,plain,
% 35.55/4.99      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 35.55/4.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_2309,plain,
% 35.55/4.99      ( m1_subset_1(k2_lattices(sK2,sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
% 35.55/4.99      inference(global_propositional_subsumption,
% 35.55/4.99                [status(thm)],
% 35.55/4.99                [c_1891,c_29,c_31]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_12,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 35.55/4.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 35.55/4.99      | ~ l2_lattices(X1)
% 35.55/4.99      | ~ v4_lattices(X1)
% 35.55/4.99      | v2_struct_0(X1)
% 35.55/4.99      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
% 35.55/4.99      inference(cnf_transformation,[],[f53]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_2,plain,
% 35.55/4.99      ( v4_lattices(X0)
% 35.55/4.99      | ~ l3_lattices(X0)
% 35.55/4.99      | v2_struct_0(X0)
% 35.55/4.99      | ~ v10_lattices(X0) ),
% 35.55/4.99      inference(cnf_transformation,[],[f42]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_268,plain,
% 35.55/4.99      ( v4_lattices(X0)
% 35.55/4.99      | ~ l3_lattices(X0)
% 35.55/4.99      | v2_struct_0(X0)
% 35.55/4.99      | sK2 != X0 ),
% 35.55/4.99      inference(resolution_lifted,[status(thm)],[c_2,c_23]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_269,plain,
% 35.55/4.99      ( v4_lattices(sK2) | ~ l3_lattices(sK2) | v2_struct_0(sK2) ),
% 35.55/4.99      inference(unflattening,[status(thm)],[c_268]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_67,plain,
% 35.55/4.99      ( v4_lattices(sK2)
% 35.55/4.99      | ~ l3_lattices(sK2)
% 35.55/4.99      | v2_struct_0(sK2)
% 35.55/4.99      | ~ v10_lattices(sK2) ),
% 35.55/4.99      inference(instantiation,[status(thm)],[c_2]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_271,plain,
% 35.55/4.99      ( v4_lattices(sK2) ),
% 35.55/4.99      inference(global_propositional_subsumption,
% 35.55/4.99                [status(thm)],
% 35.55/4.99                [c_269,c_24,c_23,c_21,c_67]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_357,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 35.55/4.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 35.55/4.99      | ~ l2_lattices(X1)
% 35.55/4.99      | v2_struct_0(X1)
% 35.55/4.99      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0)
% 35.55/4.99      | sK2 != X1 ),
% 35.55/4.99      inference(resolution_lifted,[status(thm)],[c_12,c_271]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_358,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 35.55/4.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 35.55/4.99      | ~ l2_lattices(sK2)
% 35.55/4.99      | v2_struct_0(sK2)
% 35.55/4.99      | k1_lattices(sK2,X0,X1) = k3_lattices(sK2,X0,X1) ),
% 35.55/4.99      inference(unflattening,[status(thm)],[c_357]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_10,plain,
% 35.55/4.99      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 35.55/4.99      inference(cnf_transformation,[],[f52]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_45,plain,
% 35.55/4.99      ( l2_lattices(sK2) | ~ l3_lattices(sK2) ),
% 35.55/4.99      inference(instantiation,[status(thm)],[c_10]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_362,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 35.55/4.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 35.55/4.99      | k1_lattices(sK2,X0,X1) = k3_lattices(sK2,X0,X1) ),
% 35.55/4.99      inference(global_propositional_subsumption,
% 35.55/4.99                [status(thm)],
% 35.55/4.99                [c_358,c_24,c_21,c_45]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_503,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
% 35.55/4.99      | ~ m1_subset_1(X1_49,u1_struct_0(sK2))
% 35.55/4.99      | k1_lattices(sK2,X0_49,X1_49) = k3_lattices(sK2,X0_49,X1_49) ),
% 35.55/4.99      inference(subtyping,[status(esa)],[c_362]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_682,plain,
% 35.55/4.99      ( k1_lattices(sK2,X0_49,X1_49) = k3_lattices(sK2,X0_49,X1_49)
% 35.55/4.99      | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
% 35.55/4.99      | m1_subset_1(X1_49,u1_struct_0(sK2)) != iProver_top ),
% 35.55/4.99      inference(predicate_to_equality,[status(thm)],[c_503]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_2555,plain,
% 35.55/4.99      ( k1_lattices(sK2,k2_lattices(sK2,sK3,sK4),X0_49) = k3_lattices(sK2,k2_lattices(sK2,sK3,sK4),X0_49)
% 35.55/4.99      | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
% 35.55/4.99      inference(superposition,[status(thm)],[c_2309,c_682]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_36798,plain,
% 35.55/4.99      ( k1_lattices(sK2,k2_lattices(sK2,sK3,sK4),sK4) = k3_lattices(sK2,k2_lattices(sK2,sK3,sK4),sK4) ),
% 35.55/4.99      inference(superposition,[status(thm)],[c_677,c_2555]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_8,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 35.55/4.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 35.55/4.99      | ~ l3_lattices(X1)
% 35.55/4.99      | v2_struct_0(X1)
% 35.55/4.99      | ~ v8_lattices(X1)
% 35.55/4.99      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 ),
% 35.55/4.99      inference(cnf_transformation,[],[f46]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_413,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 35.55/4.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 35.55/4.99      | ~ l3_lattices(X1)
% 35.55/4.99      | ~ v8_lattices(X1)
% 35.55/4.99      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
% 35.55/4.99      | sK2 != X1 ),
% 35.55/4.99      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_414,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 35.55/4.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 35.55/4.99      | ~ l3_lattices(sK2)
% 35.55/4.99      | ~ v8_lattices(sK2)
% 35.55/4.99      | k1_lattices(sK2,k2_lattices(sK2,X0,X1),X1) = X1 ),
% 35.55/4.99      inference(unflattening,[status(thm)],[c_413]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_0,plain,
% 35.55/4.99      ( ~ l3_lattices(X0)
% 35.55/4.99      | v2_struct_0(X0)
% 35.55/4.99      | ~ v10_lattices(X0)
% 35.55/4.99      | v8_lattices(X0) ),
% 35.55/4.99      inference(cnf_transformation,[],[f44]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_73,plain,
% 35.55/4.99      ( ~ l3_lattices(sK2)
% 35.55/4.99      | v2_struct_0(sK2)
% 35.55/4.99      | ~ v10_lattices(sK2)
% 35.55/4.99      | v8_lattices(sK2) ),
% 35.55/4.99      inference(instantiation,[status(thm)],[c_0]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_418,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 35.55/4.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 35.55/4.99      | k1_lattices(sK2,k2_lattices(sK2,X0,X1),X1) = X1 ),
% 35.55/4.99      inference(global_propositional_subsumption,
% 35.55/4.99                [status(thm)],
% 35.55/4.99                [c_414,c_24,c_23,c_21,c_73]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_501,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
% 35.55/4.99      | ~ m1_subset_1(X1_49,u1_struct_0(sK2))
% 35.55/4.99      | k1_lattices(sK2,k2_lattices(sK2,X0_49,X1_49),X1_49) = X1_49 ),
% 35.55/4.99      inference(subtyping,[status(esa)],[c_418]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_684,plain,
% 35.55/4.99      ( k1_lattices(sK2,k2_lattices(sK2,X0_49,X1_49),X1_49) = X1_49
% 35.55/4.99      | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
% 35.55/4.99      | m1_subset_1(X1_49,u1_struct_0(sK2)) != iProver_top ),
% 35.55/4.99      inference(predicate_to_equality,[status(thm)],[c_501]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_850,plain,
% 35.55/4.99      ( k1_lattices(sK2,k2_lattices(sK2,sK3,X0_49),X0_49) = X0_49
% 35.55/4.99      | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
% 35.55/4.99      inference(superposition,[status(thm)],[c_678,c_684]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_1173,plain,
% 35.55/4.99      ( k1_lattices(sK2,k2_lattices(sK2,sK3,sK4),sK4) = sK4 ),
% 35.55/4.99      inference(superposition,[status(thm)],[c_677,c_850]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_4,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 35.55/4.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 35.55/4.99      | ~ l2_lattices(X1)
% 35.55/4.99      | ~ v4_lattices(X1)
% 35.55/4.99      | v2_struct_0(X1)
% 35.55/4.99      | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
% 35.55/4.99      inference(cnf_transformation,[],[f45]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_378,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 35.55/4.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 35.55/4.99      | ~ l2_lattices(X1)
% 35.55/4.99      | v2_struct_0(X1)
% 35.55/4.99      | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
% 35.55/4.99      | sK2 != X1 ),
% 35.55/4.99      inference(resolution_lifted,[status(thm)],[c_4,c_271]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_379,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 35.55/4.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 35.55/4.99      | ~ l2_lattices(sK2)
% 35.55/4.99      | v2_struct_0(sK2)
% 35.55/4.99      | k3_lattices(sK2,X0,X1) = k3_lattices(sK2,X1,X0) ),
% 35.55/4.99      inference(unflattening,[status(thm)],[c_378]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_383,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 35.55/4.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 35.55/4.99      | k3_lattices(sK2,X0,X1) = k3_lattices(sK2,X1,X0) ),
% 35.55/4.99      inference(global_propositional_subsumption,
% 35.55/4.99                [status(thm)],
% 35.55/4.99                [c_379,c_24,c_21,c_45]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_502,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
% 35.55/4.99      | ~ m1_subset_1(X1_49,u1_struct_0(sK2))
% 35.55/4.99      | k3_lattices(sK2,X0_49,X1_49) = k3_lattices(sK2,X1_49,X0_49) ),
% 35.55/4.99      inference(subtyping,[status(esa)],[c_383]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_683,plain,
% 35.55/4.99      ( k3_lattices(sK2,X0_49,X1_49) = k3_lattices(sK2,X1_49,X0_49)
% 35.55/4.99      | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
% 35.55/4.99      | m1_subset_1(X1_49,u1_struct_0(sK2)) != iProver_top ),
% 35.55/4.99      inference(predicate_to_equality,[status(thm)],[c_502]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_3531,plain,
% 35.55/4.99      ( k3_lattices(sK2,sK4,X0_49) = k3_lattices(sK2,X0_49,sK4)
% 35.55/4.99      | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
% 35.55/4.99      inference(superposition,[status(thm)],[c_677,c_683]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_3858,plain,
% 35.55/4.99      ( k3_lattices(sK2,sK4,k2_lattices(sK2,sK3,sK4)) = k3_lattices(sK2,k2_lattices(sK2,sK3,sK4),sK4) ),
% 35.55/4.99      inference(superposition,[status(thm)],[c_2309,c_3531]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_36810,plain,
% 35.55/4.99      ( k3_lattices(sK2,sK4,k2_lattices(sK2,sK3,sK4)) = sK4 ),
% 35.55/4.99      inference(light_normalisation,
% 35.55/4.99                [status(thm)],
% 35.55/4.99                [c_36798,c_1173,c_3858]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_509,negated_conjecture,
% 35.55/4.99      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 35.55/4.99      inference(subtyping,[status(esa)],[c_18]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_676,plain,
% 35.55/4.99      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 35.55/4.99      inference(predicate_to_equality,[status(thm)],[c_509]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_36797,plain,
% 35.55/4.99      ( k1_lattices(sK2,k2_lattices(sK2,sK3,sK4),sK5) = k3_lattices(sK2,k2_lattices(sK2,sK3,sK4),sK5) ),
% 35.55/4.99      inference(superposition,[status(thm)],[c_676,c_2555]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_1821,plain,
% 35.55/4.99      ( k4_lattices(sK2,sK3,sK5) = k2_lattices(sK2,sK3,sK5) ),
% 35.55/4.99      inference(superposition,[status(thm)],[c_676,c_1308]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_1933,plain,
% 35.55/4.99      ( k4_lattices(sK2,sK3,sK4) = k2_lattices(sK2,sK3,sK5) ),
% 35.55/4.99      inference(demodulation,[status(thm)],[c_1821,c_510]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_1934,plain,
% 35.55/4.99      ( k2_lattices(sK2,sK3,sK4) = k2_lattices(sK2,sK3,sK5) ),
% 35.55/4.99      inference(light_normalisation,[status(thm)],[c_1933,c_1822]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_1172,plain,
% 35.55/4.99      ( k1_lattices(sK2,k2_lattices(sK2,sK3,sK5),sK5) = sK5 ),
% 35.55/4.99      inference(superposition,[status(thm)],[c_676,c_850]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_2088,plain,
% 35.55/4.99      ( k1_lattices(sK2,k2_lattices(sK2,sK3,sK4),sK5) = sK5 ),
% 35.55/4.99      inference(demodulation,[status(thm)],[c_1934,c_1172]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_3530,plain,
% 35.55/4.99      ( k3_lattices(sK2,sK5,X0_49) = k3_lattices(sK2,X0_49,sK5)
% 35.55/4.99      | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
% 35.55/4.99      inference(superposition,[status(thm)],[c_676,c_683]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_3553,plain,
% 35.55/4.99      ( k3_lattices(sK2,sK5,k2_lattices(sK2,sK3,sK4)) = k3_lattices(sK2,k2_lattices(sK2,sK3,sK4),sK5) ),
% 35.55/4.99      inference(superposition,[status(thm)],[c_2309,c_3530]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_14,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 35.55/4.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 35.55/4.99      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 35.55/4.99      | ~ v11_lattices(X1)
% 35.55/4.99      | ~ l3_lattices(X1)
% 35.55/4.99      | v2_struct_0(X1)
% 35.55/4.99      | ~ v10_lattices(X1)
% 35.55/4.99      | k4_lattices(X1,k3_lattices(X1,X2,X0),k3_lattices(X1,X2,X3)) = k3_lattices(X1,X2,k4_lattices(X1,X0,X3)) ),
% 35.55/4.99      inference(cnf_transformation,[],[f55]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_22,negated_conjecture,
% 35.55/4.99      ( v11_lattices(sK2) ),
% 35.55/4.99      inference(cnf_transformation,[],[f58]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_239,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 35.55/4.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 35.55/4.99      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 35.55/4.99      | ~ l3_lattices(X1)
% 35.55/4.99      | v2_struct_0(X1)
% 35.55/4.99      | ~ v10_lattices(X1)
% 35.55/4.99      | k4_lattices(X1,k3_lattices(X1,X2,X0),k3_lattices(X1,X2,X3)) = k3_lattices(X1,X2,k4_lattices(X1,X0,X3))
% 35.55/4.99      | sK2 != X1 ),
% 35.55/4.99      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_240,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 35.55/4.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 35.55/4.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 35.55/4.99      | ~ l3_lattices(sK2)
% 35.55/4.99      | v2_struct_0(sK2)
% 35.55/4.99      | ~ v10_lattices(sK2)
% 35.55/4.99      | k4_lattices(sK2,k3_lattices(sK2,X1,X2),k3_lattices(sK2,X1,X0)) = k3_lattices(sK2,X1,k4_lattices(sK2,X2,X0)) ),
% 35.55/4.99      inference(unflattening,[status(thm)],[c_239]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_244,plain,
% 35.55/4.99      ( ~ m1_subset_1(X2,u1_struct_0(sK2))
% 35.55/4.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 35.55/4.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 35.55/4.99      | k4_lattices(sK2,k3_lattices(sK2,X1,X2),k3_lattices(sK2,X1,X0)) = k3_lattices(sK2,X1,k4_lattices(sK2,X2,X0)) ),
% 35.55/4.99      inference(global_propositional_subsumption,
% 35.55/4.99                [status(thm)],
% 35.55/4.99                [c_240,c_24,c_23,c_21]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_245,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 35.55/4.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 35.55/4.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 35.55/4.99      | k4_lattices(sK2,k3_lattices(sK2,X2,X0),k3_lattices(sK2,X2,X1)) = k3_lattices(sK2,X2,k4_lattices(sK2,X0,X1)) ),
% 35.55/4.99      inference(renaming,[status(thm)],[c_244]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_506,plain,
% 35.55/4.99      ( ~ m1_subset_1(X0_49,u1_struct_0(sK2))
% 35.55/4.99      | ~ m1_subset_1(X1_49,u1_struct_0(sK2))
% 35.55/4.99      | ~ m1_subset_1(X2_49,u1_struct_0(sK2))
% 35.55/4.99      | k4_lattices(sK2,k3_lattices(sK2,X2_49,X0_49),k3_lattices(sK2,X2_49,X1_49)) = k3_lattices(sK2,X2_49,k4_lattices(sK2,X0_49,X1_49)) ),
% 35.55/4.99      inference(subtyping,[status(esa)],[c_245]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_679,plain,
% 35.55/4.99      ( k4_lattices(sK2,k3_lattices(sK2,X0_49,X1_49),k3_lattices(sK2,X0_49,X2_49)) = k3_lattices(sK2,X0_49,k4_lattices(sK2,X1_49,X2_49))
% 35.55/4.99      | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
% 35.55/4.99      | m1_subset_1(X1_49,u1_struct_0(sK2)) != iProver_top
% 35.55/4.99      | m1_subset_1(X2_49,u1_struct_0(sK2)) != iProver_top ),
% 35.55/4.99      inference(predicate_to_equality,[status(thm)],[c_506]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_912,plain,
% 35.55/4.99      ( k4_lattices(sK2,k3_lattices(sK2,X0_49,X1_49),k3_lattices(sK2,X0_49,sK4)) = k3_lattices(sK2,X0_49,k4_lattices(sK2,X1_49,sK4))
% 35.55/4.99      | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
% 35.55/4.99      | m1_subset_1(X1_49,u1_struct_0(sK2)) != iProver_top ),
% 35.55/4.99      inference(superposition,[status(thm)],[c_677,c_679]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_2532,plain,
% 35.55/4.99      ( k4_lattices(sK2,k3_lattices(sK2,sK5,X0_49),k3_lattices(sK2,sK5,sK4)) = k3_lattices(sK2,sK5,k4_lattices(sK2,X0_49,sK4))
% 35.55/4.99      | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
% 35.55/4.99      inference(superposition,[status(thm)],[c_676,c_912]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_3550,plain,
% 35.55/4.99      ( k3_lattices(sK2,sK5,sK4) = k3_lattices(sK2,sK4,sK5) ),
% 35.55/4.99      inference(superposition,[status(thm)],[c_677,c_3530]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_4190,plain,
% 35.55/4.99      ( k4_lattices(sK2,k3_lattices(sK2,sK5,X0_49),k3_lattices(sK2,sK4,sK5)) = k3_lattices(sK2,sK5,k4_lattices(sK2,X0_49,sK4))
% 35.55/4.99      | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
% 35.55/4.99      inference(light_normalisation,[status(thm)],[c_2532,c_3550]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_4196,plain,
% 35.55/4.99      ( k4_lattices(sK2,k3_lattices(sK2,sK5,sK3),k3_lattices(sK2,sK4,sK5)) = k3_lattices(sK2,sK5,k4_lattices(sK2,sK3,sK4)) ),
% 35.55/4.99      inference(superposition,[status(thm)],[c_678,c_4190]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_911,plain,
% 35.55/4.99      ( k4_lattices(sK2,k3_lattices(sK2,X0_49,X1_49),k3_lattices(sK2,X0_49,sK5)) = k3_lattices(sK2,X0_49,k4_lattices(sK2,X1_49,sK5))
% 35.55/4.99      | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top
% 35.55/4.99      | m1_subset_1(X1_49,u1_struct_0(sK2)) != iProver_top ),
% 35.55/4.99      inference(superposition,[status(thm)],[c_676,c_679]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_1293,plain,
% 35.55/4.99      ( k4_lattices(sK2,k3_lattices(sK2,sK4,X0_49),k3_lattices(sK2,sK4,sK5)) = k3_lattices(sK2,sK4,k4_lattices(sK2,X0_49,sK5))
% 35.55/4.99      | m1_subset_1(X0_49,u1_struct_0(sK2)) != iProver_top ),
% 35.55/4.99      inference(superposition,[status(thm)],[c_677,c_911]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_2453,plain,
% 35.55/4.99      ( k4_lattices(sK2,k3_lattices(sK2,sK4,sK3),k3_lattices(sK2,sK4,sK5)) = k3_lattices(sK2,sK4,k4_lattices(sK2,sK3,sK5)) ),
% 35.55/4.99      inference(superposition,[status(thm)],[c_678,c_1293]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_2087,plain,
% 35.55/4.99      ( k4_lattices(sK2,sK3,sK5) = k2_lattices(sK2,sK3,sK4) ),
% 35.55/4.99      inference(demodulation,[status(thm)],[c_1934,c_1821]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_2456,plain,
% 35.55/4.99      ( k4_lattices(sK2,k3_lattices(sK2,sK4,sK3),k3_lattices(sK2,sK4,sK5)) = k3_lattices(sK2,sK4,k2_lattices(sK2,sK3,sK4)) ),
% 35.55/4.99      inference(light_normalisation,[status(thm)],[c_2453,c_2087]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_3856,plain,
% 35.55/4.99      ( k3_lattices(sK2,sK4,sK3) = k3_lattices(sK2,sK3,sK4) ),
% 35.55/4.99      inference(superposition,[status(thm)],[c_678,c_3531]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_3551,plain,
% 35.55/4.99      ( k3_lattices(sK2,sK5,sK3) = k3_lattices(sK2,sK3,sK5) ),
% 35.55/4.99      inference(superposition,[status(thm)],[c_678,c_3530]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_16,negated_conjecture,
% 35.55/4.99      ( k3_lattices(sK2,sK3,sK4) = k3_lattices(sK2,sK3,sK5) ),
% 35.55/4.99      inference(cnf_transformation,[],[f64]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_511,negated_conjecture,
% 35.55/4.99      ( k3_lattices(sK2,sK3,sK4) = k3_lattices(sK2,sK3,sK5) ),
% 35.55/4.99      inference(subtyping,[status(esa)],[c_16]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_3613,plain,
% 35.55/4.99      ( k3_lattices(sK2,sK5,sK3) = k3_lattices(sK2,sK3,sK4) ),
% 35.55/4.99      inference(demodulation,[status(thm)],[c_3551,c_511]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_3878,plain,
% 35.55/4.99      ( k3_lattices(sK2,sK4,sK3) = k3_lattices(sK2,sK5,sK3) ),
% 35.55/4.99      inference(demodulation,[status(thm)],[c_3856,c_3613]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_4199,plain,
% 35.55/4.99      ( k3_lattices(sK2,sK5,k2_lattices(sK2,sK3,sK4)) = k3_lattices(sK2,sK4,k2_lattices(sK2,sK3,sK4)) ),
% 35.55/4.99      inference(light_normalisation,
% 35.55/4.99                [status(thm)],
% 35.55/4.99                [c_4196,c_1822,c_2456,c_3878]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_5748,plain,
% 35.55/4.99      ( k3_lattices(sK2,k2_lattices(sK2,sK3,sK4),sK5) = k3_lattices(sK2,sK4,k2_lattices(sK2,sK3,sK4)) ),
% 35.55/4.99      inference(light_normalisation,[status(thm)],[c_3553,c_3553,c_4199]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_36811,plain,
% 35.55/4.99      ( k3_lattices(sK2,sK4,k2_lattices(sK2,sK3,sK4)) = sK5 ),
% 35.55/4.99      inference(light_normalisation,
% 35.55/4.99                [status(thm)],
% 35.55/4.99                [c_36797,c_2088,c_5748]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_37116,plain,
% 35.55/4.99      ( sK5 = sK4 ),
% 35.55/4.99      inference(superposition,[status(thm)],[c_36810,c_36811]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_514,plain,( X0_49 = X0_49 ),theory(equality) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_862,plain,
% 35.55/4.99      ( sK4 = sK4 ),
% 35.55/4.99      inference(instantiation,[status(thm)],[c_514]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_15,negated_conjecture,
% 35.55/4.99      ( sK4 != sK5 ),
% 35.55/4.99      inference(cnf_transformation,[],[f65]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(c_512,negated_conjecture,
% 35.55/4.99      ( sK4 != sK5 ),
% 35.55/4.99      inference(subtyping,[status(esa)],[c_15]) ).
% 35.55/4.99  
% 35.55/4.99  cnf(contradiction,plain,
% 35.55/4.99      ( $false ),
% 35.55/4.99      inference(minisat,[status(thm)],[c_127738,c_37116,c_862,c_512]) ).
% 35.55/4.99  
% 35.55/4.99  
% 35.55/4.99  % SZS output end CNFRefutation for theBenchmark.p
% 35.55/4.99  
% 35.55/4.99  ------                               Statistics
% 35.55/4.99  
% 35.55/4.99  ------ General
% 35.55/4.99  
% 35.55/4.99  abstr_ref_over_cycles:                  0
% 35.55/4.99  abstr_ref_under_cycles:                 0
% 35.55/4.99  gc_basic_clause_elim:                   0
% 35.55/4.99  forced_gc_time:                         0
% 35.55/4.99  parsing_time:                           0.011
% 35.55/4.99  unif_index_cands_time:                  0.
% 35.55/4.99  unif_index_add_time:                    0.
% 35.55/4.99  orderings_time:                         0.
% 35.55/4.99  out_proof_time:                         0.016
% 35.55/4.99  total_time:                             4.303
% 35.55/4.99  num_of_symbols:                         52
% 35.55/4.99  num_of_terms:                           89227
% 35.55/4.99  
% 35.55/4.99  ------ Preprocessing
% 35.55/4.99  
% 35.55/4.99  num_of_splits:                          0
% 35.55/4.99  num_of_split_atoms:                     0
% 35.55/4.99  num_of_reused_defs:                     0
% 35.55/4.99  num_eq_ax_congr_red:                    21
% 35.55/4.99  num_of_sem_filtered_clauses:            1
% 35.55/4.99  num_of_subtypes:                        3
% 35.55/4.99  monotx_restored_types:                  0
% 35.55/4.99  sat_num_of_epr_types:                   0
% 35.55/4.99  sat_num_of_non_cyclic_types:            0
% 35.55/4.99  sat_guarded_non_collapsed_types:        1
% 35.55/4.99  num_pure_diseq_elim:                    0
% 35.55/4.99  simp_replaced_by:                       0
% 35.55/4.99  res_preprocessed:                       73
% 35.55/4.99  prep_upred:                             0
% 35.55/4.99  prep_unflattend:                        12
% 35.55/4.99  smt_new_axioms:                         0
% 35.55/4.99  pred_elim_cands:                        1
% 35.55/4.99  pred_elim:                              9
% 35.55/4.99  pred_elim_cl:                           12
% 35.55/4.99  pred_elim_cycles:                       11
% 35.55/4.99  merged_defs:                            0
% 35.55/4.99  merged_defs_ncl:                        0
% 35.55/4.99  bin_hyper_res:                          0
% 35.55/4.99  prep_cycles:                            4
% 35.55/4.99  pred_elim_time:                         0.003
% 35.55/4.99  splitting_time:                         0.
% 35.55/4.99  sem_filter_time:                        0.
% 35.55/4.99  monotx_time:                            0.
% 35.55/4.99  subtype_inf_time:                       0.
% 35.55/4.99  
% 35.55/4.99  ------ Problem properties
% 35.55/4.99  
% 35.55/4.99  clauses:                                12
% 35.55/4.99  conjectures:                            6
% 35.55/4.99  epr:                                    1
% 35.55/4.99  horn:                                   12
% 35.55/4.99  ground:                                 6
% 35.55/4.99  unary:                                  6
% 35.55/4.99  binary:                                 0
% 35.55/4.99  lits:                                   25
% 35.55/4.99  lits_eq:                                8
% 35.55/4.99  fd_pure:                                0
% 35.55/4.99  fd_pseudo:                              0
% 35.55/4.99  fd_cond:                                0
% 35.55/4.99  fd_pseudo_cond:                         0
% 35.55/4.99  ac_symbols:                             0
% 35.55/4.99  
% 35.55/4.99  ------ Propositional Solver
% 35.55/4.99  
% 35.55/4.99  prop_solver_calls:                      53
% 35.55/4.99  prop_fast_solver_calls:                 2246
% 35.55/4.99  smt_solver_calls:                       0
% 35.55/4.99  smt_fast_solver_calls:                  0
% 35.55/4.99  prop_num_of_clauses:                    33719
% 35.55/4.99  prop_preprocess_simplified:             64742
% 35.55/4.99  prop_fo_subsumed:                       42
% 35.55/4.99  prop_solver_time:                       0.
% 35.55/4.99  smt_solver_time:                        0.
% 35.55/4.99  smt_fast_solver_time:                   0.
% 35.55/4.99  prop_fast_solver_time:                  0.
% 35.55/4.99  prop_unsat_core_time:                   0.004
% 35.55/4.99  
% 35.55/4.99  ------ QBF
% 35.55/4.99  
% 35.55/4.99  qbf_q_res:                              0
% 35.55/4.99  qbf_num_tautologies:                    0
% 35.55/4.99  qbf_prep_cycles:                        0
% 35.55/4.99  
% 35.55/4.99  ------ BMC1
% 35.55/4.99  
% 35.55/4.99  bmc1_current_bound:                     -1
% 35.55/4.99  bmc1_last_solved_bound:                 -1
% 35.55/4.99  bmc1_unsat_core_size:                   -1
% 35.55/4.99  bmc1_unsat_core_parents_size:           -1
% 35.55/4.99  bmc1_merge_next_fun:                    0
% 35.55/4.99  bmc1_unsat_core_clauses_time:           0.
% 35.55/4.99  
% 35.55/4.99  ------ Instantiation
% 35.55/4.99  
% 35.55/4.99  inst_num_of_clauses:                    5698
% 35.55/4.99  inst_num_in_passive:                    1963
% 35.55/4.99  inst_num_in_active:                     4619
% 35.55/4.99  inst_num_in_unprocessed:                1853
% 35.55/4.99  inst_num_of_loops:                      5000
% 35.55/4.99  inst_num_of_learning_restarts:          1
% 35.55/4.99  inst_num_moves_active_passive:          361
% 35.55/4.99  inst_lit_activity:                      0
% 35.55/4.99  inst_lit_activity_moves:                3
% 35.55/4.99  inst_num_tautologies:                   0
% 35.55/4.99  inst_num_prop_implied:                  0
% 35.55/4.99  inst_num_existing_simplified:           0
% 35.55/4.99  inst_num_eq_res_simplified:             0
% 35.55/4.99  inst_num_child_elim:                    0
% 35.55/4.99  inst_num_of_dismatching_blockings:      23375
% 35.55/4.99  inst_num_of_non_proper_insts:           28062
% 35.55/4.99  inst_num_of_duplicates:                 0
% 35.55/4.99  inst_inst_num_from_inst_to_res:         0
% 35.55/4.99  inst_dismatching_checking_time:         0.
% 35.55/4.99  
% 35.55/4.99  ------ Resolution
% 35.55/4.99  
% 35.55/4.99  res_num_of_clauses:                     18
% 35.55/4.99  res_num_in_passive:                     18
% 35.55/4.99  res_num_in_active:                      0
% 35.55/4.99  res_num_of_loops:                       77
% 35.55/4.99  res_forward_subset_subsumed:            689
% 35.55/4.99  res_backward_subset_subsumed:           4
% 35.55/4.99  res_forward_subsumed:                   0
% 35.55/4.99  res_backward_subsumed:                  0
% 35.55/4.99  res_forward_subsumption_resolution:     0
% 35.55/4.99  res_backward_subsumption_resolution:    0
% 35.55/4.99  res_clause_to_clause_subsumption:       21947
% 35.55/4.99  res_orphan_elimination:                 0
% 35.55/4.99  res_tautology_del:                      2897
% 35.55/4.99  res_num_eq_res_simplified:              0
% 35.55/4.99  res_num_sel_changes:                    0
% 35.55/4.99  res_moves_from_active_to_pass:          0
% 35.55/4.99  
% 35.55/4.99  ------ Superposition
% 35.55/4.99  
% 35.55/4.99  sup_time_total:                         0.
% 35.55/4.99  sup_time_generating:                    0.
% 35.55/4.99  sup_time_sim_full:                      0.
% 35.55/4.99  sup_time_sim_immed:                     0.
% 35.55/4.99  
% 35.55/4.99  sup_num_of_clauses:                     5269
% 35.55/4.99  sup_num_in_active:                      904
% 35.55/4.99  sup_num_in_passive:                     4365
% 35.55/4.99  sup_num_of_loops:                       1000
% 35.55/4.99  sup_fw_superposition:                   5679
% 35.55/4.99  sup_bw_superposition:                   1993
% 35.55/4.99  sup_immediate_simplified:               4874
% 35.55/4.99  sup_given_eliminated:                   1
% 35.55/4.99  comparisons_done:                       0
% 35.55/4.99  comparisons_avoided:                    0
% 35.55/4.99  
% 35.55/4.99  ------ Simplifications
% 35.55/4.99  
% 35.55/4.99  
% 35.55/4.99  sim_fw_subset_subsumed:                 1
% 35.55/4.99  sim_bw_subset_subsumed:                 3
% 35.55/4.99  sim_fw_subsumed:                        0
% 35.55/4.99  sim_bw_subsumed:                        0
% 35.55/4.99  sim_fw_subsumption_res:                 0
% 35.55/4.99  sim_bw_subsumption_res:                 0
% 35.55/4.99  sim_tautology_del:                      0
% 35.55/4.99  sim_eq_tautology_del:                   632
% 35.55/4.99  sim_eq_res_simp:                        0
% 35.55/4.99  sim_fw_demodulated:                     1345
% 35.55/4.99  sim_bw_demodulated:                     242
% 35.55/4.99  sim_light_normalised:                   4634
% 35.55/4.99  sim_joinable_taut:                      0
% 35.55/4.99  sim_joinable_simp:                      0
% 35.55/4.99  sim_ac_normalised:                      0
% 35.55/4.99  sim_smt_subsumption:                    0
% 35.55/4.99  
%------------------------------------------------------------------------------
