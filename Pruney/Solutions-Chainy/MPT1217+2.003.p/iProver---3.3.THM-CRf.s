%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:23 EST 2020

% Result     : Theorem 1.01s
% Output     : CNFRefutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :  194 (1188 expanded)
%              Number of clauses        :  124 ( 272 expanded)
%              Number of leaves         :   16 ( 359 expanded)
%              Depth                    :   26
%              Number of atoms          :  879 (7828 expanded)
%              Number of equality atoms :  152 ( 174 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_lattices(X0,X1,X2)
               => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_lattices(X0,X1,X2)
                 => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
          & r3_lattices(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,k7_lattices(X0,sK4),k7_lattices(X0,X1))
        & r3_lattices(X0,X1,sK4)
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,sK3))
            & r3_lattices(X0,sK3,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
                & r3_lattices(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(sK2,k7_lattices(sK2,X2),k7_lattices(sK2,X1))
              & r3_lattices(sK2,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l3_lattices(sK2)
      & v17_lattices(sK2)
      & v10_lattices(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ~ r3_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3))
    & r3_lattices(sK2,sK3,sK4)
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l3_lattices(sK2)
    & v17_lattices(sK2)
    & v10_lattices(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f35,f45,f44,f43])).

fof(f71,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f13,plain,(
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

fof(f14,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f15,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f16,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f15])).

fof(f49,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f68,plain,(
    v10_lattices(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f59,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k1_lattices(X0,k2_lattices(X0,X1,sK1(X0)),sK1(X0)) != sK1(X0)
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).

fof(f53,plain,(
    ! [X4,X0,X3] :
      ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f50,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f51,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f73,plain,(
    r3_lattices(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f69,plain,(
    v17_lattices(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k2_lattices(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,(
    ~ r3_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) ),
    inference(cnf_transformation,[],[f46])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X2)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_799,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_976,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_799])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_678,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_27])).

cnf(c_679,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(k7_lattices(sK2,X0),u1_struct_0(sK2))
    | ~ l3_lattices(sK2) ),
    inference(unflattening,[status(thm)],[c_678])).

cnf(c_24,negated_conjecture,
    ( l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_683,plain,
    ( m1_subset_1(k7_lattices(sK2,X0),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_679,c_24])).

cnf(c_684,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(k7_lattices(sK2,X0),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_683])).

cnf(c_792,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | m1_subset_1(k7_lattices(sK2,X0_52),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_684])).

cnf(c_982,plain,
    ( m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k7_lattices(sK2,X0_52),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_792])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_800,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_975,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_800])).

cnf(c_12,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_301,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_12,c_14])).

cnf(c_302,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_2,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_26,negated_conjecture,
    ( v10_lattices(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_368,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_26])).

cnf(c_369,plain,
    ( v6_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_86,plain,
    ( v6_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_371,plain,
    ( v6_lattices(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_369,c_27,c_26,c_24,c_86])).

cnf(c_507,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_302,c_371])).

cnf(c_508,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | k4_lattices(sK2,X0,X1) = k2_lattices(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_512,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k4_lattices(sK2,X0,X1) = k2_lattices(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_508,c_27,c_24])).

cnf(c_795,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
    | k4_lattices(sK2,X0_52,X1_52) = k2_lattices(sK2,X0_52,X1_52) ),
    inference(subtyping,[status(esa)],[c_512])).

cnf(c_980,plain,
    ( k4_lattices(sK2,X0_52,X1_52) = k2_lattices(sK2,X0_52,X1_52)
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_795])).

cnf(c_2958,plain,
    ( k4_lattices(sK2,k7_lattices(sK2,X0_52),X1_52) = k2_lattices(sK2,k7_lattices(sK2,X0_52),X1_52)
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_982,c_980])).

cnf(c_8368,plain,
    ( k4_lattices(sK2,k7_lattices(sK2,sK4),X0_52) = k2_lattices(sK2,k7_lattices(sK2,sK4),X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_975,c_2958])).

cnf(c_8397,plain,
    ( k4_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,X0_52)) = k2_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,X0_52))
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_982,c_8368])).

cnf(c_9033,plain,
    ( k4_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) = k2_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_976,c_8397])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_357,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_26])).

cnf(c_358,plain,
    ( v4_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_83,plain,
    ( v4_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_360,plain,
    ( v4_lattices(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_358,c_27,c_26,c_24,c_83])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_360])).

cnf(c_431,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l2_lattices(sK2)
    | v2_struct_0(sK2)
    | k3_lattices(sK2,X0,X1) = k3_lattices(sK2,X1,X0) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_11,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_61,plain,
    ( l2_lattices(sK2)
    | ~ l3_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_435,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k3_lattices(sK2,X0,X1) = k3_lattices(sK2,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_431,c_27,c_24,c_61])).

cnf(c_796,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
    | k3_lattices(sK2,X0_52,X1_52) = k3_lattices(sK2,X1_52,X0_52) ),
    inference(subtyping,[status(esa)],[c_435])).

cnf(c_979,plain,
    ( k3_lattices(sK2,X0_52,X1_52) = k3_lattices(sK2,X1_52,X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_796])).

cnf(c_2389,plain,
    ( k3_lattices(sK2,X0_52,sK4) = k3_lattices(sK2,sK4,X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_975,c_979])).

cnf(c_2510,plain,
    ( k3_lattices(sK2,sK3,sK4) = k3_lattices(sK2,sK4,sK3) ),
    inference(superposition,[status(thm)],[c_976,c_2389])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_409,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_360])).

cnf(c_410,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l2_lattices(sK2)
    | v2_struct_0(sK2)
    | k1_lattices(sK2,X0,X1) = k3_lattices(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_414,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k1_lattices(sK2,X0,X1) = k3_lattices(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_410,c_27,c_24,c_61])).

cnf(c_797,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
    | k1_lattices(sK2,X0_52,X1_52) = k3_lattices(sK2,X0_52,X1_52) ),
    inference(subtyping,[status(esa)],[c_414])).

cnf(c_978,plain,
    ( k1_lattices(sK2,X0_52,X1_52) = k3_lattices(sK2,X0_52,X1_52)
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_797])).

cnf(c_1784,plain,
    ( k1_lattices(sK2,sK3,X0_52) = k3_lattices(sK2,sK3,X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_976,c_978])).

cnf(c_2013,plain,
    ( k1_lattices(sK2,sK3,sK4) = k3_lattices(sK2,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_975,c_1784])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_696,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_27])).

cnf(c_697,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v8_lattices(sK2)
    | ~ l3_lattices(sK2)
    | k1_lattices(sK2,k2_lattices(sK2,X0,X1),X1) = X1 ),
    inference(unflattening,[status(thm)],[c_696])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_89,plain,
    ( v8_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_701,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k1_lattices(sK2,k2_lattices(sK2,X0,X1),X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_697,c_27,c_26,c_24,c_89])).

cnf(c_791,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
    | k1_lattices(sK2,k2_lattices(sK2,X0_52,X1_52),X1_52) = X1_52 ),
    inference(subtyping,[status(esa)],[c_701])).

cnf(c_983,plain,
    ( k1_lattices(sK2,k2_lattices(sK2,X0_52,X1_52),X1_52) = X1_52
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_791])).

cnf(c_1108,plain,
    ( k1_lattices(sK2,k2_lattices(sK2,sK3,X0_52),X0_52) = X0_52
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_976,c_983])).

cnf(c_1390,plain,
    ( k1_lattices(sK2,k2_lattices(sK2,sK3,sK4),sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_975,c_1108])).

cnf(c_18,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_390,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v9_lattices(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_26])).

cnf(c_391,plain,
    ( ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | v9_lattices(sK2) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_92,plain,
    ( ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2)
    | v9_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_393,plain,
    ( v9_lattices(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_391,c_27,c_26,c_24,c_92])).

cnf(c_586,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_393])).

cnf(c_587,plain,
    ( ~ r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v8_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | k2_lattices(sK2,X0,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_586])).

cnf(c_591,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r1_lattices(sK2,X0,X1)
    | k2_lattices(sK2,X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_587,c_27,c_26,c_24,c_89])).

cnf(c_592,plain,
    ( ~ r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k2_lattices(sK2,X0,X1) = X0 ),
    inference(renaming,[status(thm)],[c_591])).

cnf(c_21,negated_conjecture,
    ( r3_lattices(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_16,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_459,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_371])).

cnf(c_460,plain,
    ( r1_lattices(sK2,X0,X1)
    | ~ r3_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v8_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v9_lattices(sK2) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_464,plain,
    ( r1_lattices(sK2,X0,X1)
    | ~ r3_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_460,c_27,c_26,c_24,c_89,c_92])).

cnf(c_465,plain,
    ( r1_lattices(sK2,X0,X1)
    | ~ r3_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_464])).

cnf(c_566,plain,
    ( r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | sK3 != X0
    | sK4 != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_465])).

cnf(c_567,plain,
    ( r1_lattices(sK2,sK3,sK4)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_566])).

cnf(c_569,plain,
    ( r1_lattices(sK2,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_567,c_23,c_22])).

cnf(c_658,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k2_lattices(sK2,X0,X1) = X0
    | sK3 != X0
    | sK4 != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_592,c_569])).

cnf(c_659,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | k2_lattices(sK2,sK3,sK4) = sK3 ),
    inference(unflattening,[status(thm)],[c_658])).

cnf(c_661,plain,
    ( k2_lattices(sK2,sK3,sK4) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_659,c_23,c_22])).

cnf(c_793,plain,
    ( k2_lattices(sK2,sK3,sK4) = sK3 ),
    inference(subtyping,[status(esa)],[c_661])).

cnf(c_1400,plain,
    ( k1_lattices(sK2,sK3,sK4) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_1390,c_793])).

cnf(c_2023,plain,
    ( k3_lattices(sK2,sK3,sK4) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_2013,c_1400])).

cnf(c_2517,plain,
    ( k3_lattices(sK2,sK4,sK3) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_2510,c_2023])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k3_lattices(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_25,negated_conjecture,
    ( v17_lattices(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_332,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k3_lattices(X1,X2,X0))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_333,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2)
    | k4_lattices(sK2,k7_lattices(sK2,X0),k7_lattices(sK2,X1)) = k7_lattices(sK2,k3_lattices(sK2,X0,X1)) ),
    inference(unflattening,[status(thm)],[c_332])).

cnf(c_337,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k4_lattices(sK2,k7_lattices(sK2,X0),k7_lattices(sK2,X1)) = k7_lattices(sK2,k3_lattices(sK2,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_333,c_27,c_26,c_24])).

cnf(c_338,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k4_lattices(sK2,k7_lattices(sK2,X0),k7_lattices(sK2,X1)) = k7_lattices(sK2,k3_lattices(sK2,X0,X1)) ),
    inference(renaming,[status(thm)],[c_337])).

cnf(c_798,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
    | k4_lattices(sK2,k7_lattices(sK2,X0_52),k7_lattices(sK2,X1_52)) = k7_lattices(sK2,k3_lattices(sK2,X0_52,X1_52)) ),
    inference(subtyping,[status(esa)],[c_338])).

cnf(c_977,plain,
    ( k4_lattices(sK2,k7_lattices(sK2,X0_52),k7_lattices(sK2,X1_52)) = k7_lattices(sK2,k3_lattices(sK2,X0_52,X1_52))
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_798])).

cnf(c_1245,plain,
    ( k4_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,X0_52)) = k7_lattices(sK2,k3_lattices(sK2,sK4,X0_52))
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_975,c_977])).

cnf(c_1463,plain,
    ( k4_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) = k7_lattices(sK2,k3_lattices(sK2,sK4,sK3)) ),
    inference(superposition,[status(thm)],[c_976,c_1245])).

cnf(c_2682,plain,
    ( k4_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) = k7_lattices(sK2,sK4) ),
    inference(demodulation,[status(thm)],[c_2517,c_1463])).

cnf(c_9040,plain,
    ( k2_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) = k7_lattices(sK2,sK4) ),
    inference(light_normalisation,[status(thm)],[c_9033,c_2682])).

cnf(c_1053,plain,
    ( m1_subset_1(k7_lattices(sK2,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_832,plain,
    ( m1_subset_1(k7_lattices(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_17,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) != X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_610,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_393])).

cnf(c_611,plain,
    ( r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v8_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | k2_lattices(sK2,X0,X1) != X0 ),
    inference(unflattening,[status(thm)],[c_610])).

cnf(c_615,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r1_lattices(sK2,X0,X1)
    | k2_lattices(sK2,X0,X1) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_611,c_27,c_26,c_24,c_89])).

cnf(c_616,plain,
    ( r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k2_lattices(sK2,X0,X1) != X0 ),
    inference(renaming,[status(thm)],[c_615])).

cnf(c_20,negated_conjecture,
    ( ~ r3_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_15,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_483,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_371])).

cnf(c_484,plain,
    ( ~ r1_lattices(sK2,X0,X1)
    | r3_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v8_lattices(sK2)
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v9_lattices(sK2) ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_488,plain,
    ( ~ r1_lattices(sK2,X0,X1)
    | r3_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_484,c_27,c_26,c_24,c_89,c_92])).

cnf(c_489,plain,
    ( ~ r1_lattices(sK2,X0,X1)
    | r3_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_488])).

cnf(c_553,plain,
    ( ~ r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k7_lattices(sK2,sK3) != X1
    | k7_lattices(sK2,sK4) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_489])).

cnf(c_554,plain,
    ( ~ r1_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3))
    | ~ m1_subset_1(k7_lattices(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k7_lattices(sK2,sK4),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_645,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k7_lattices(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k7_lattices(sK2,sK4),u1_struct_0(sK2))
    | k2_lattices(sK2,X0,X1) != X0
    | k7_lattices(sK2,sK3) != X1
    | k7_lattices(sK2,sK4) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_616,c_554])).

cnf(c_646,plain,
    ( ~ m1_subset_1(k7_lattices(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k7_lattices(sK2,sK4),u1_struct_0(sK2))
    | k2_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) != k7_lattices(sK2,sK4) ),
    inference(unflattening,[status(thm)],[c_645])).

cnf(c_794,plain,
    ( ~ m1_subset_1(k7_lattices(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k7_lattices(sK2,sK4),u1_struct_0(sK2))
    | k2_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) != k7_lattices(sK2,sK4) ),
    inference(subtyping,[status(esa)],[c_646])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9040,c_1053,c_832,c_794,c_22,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:47:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  % Running in FOF mode
% 1.01/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.01/1.03  
% 1.01/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.01/1.03  
% 1.01/1.03  ------  iProver source info
% 1.01/1.03  
% 1.01/1.03  git: date: 2020-06-30 10:37:57 +0100
% 1.01/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.01/1.03  git: non_committed_changes: false
% 1.01/1.03  git: last_make_outside_of_git: false
% 1.01/1.03  
% 1.01/1.03  ------ 
% 1.01/1.03  
% 1.01/1.03  ------ Input Options
% 1.01/1.03  
% 1.01/1.03  --out_options                           all
% 1.01/1.03  --tptp_safe_out                         true
% 1.01/1.03  --problem_path                          ""
% 1.01/1.03  --include_path                          ""
% 1.01/1.03  --clausifier                            res/vclausify_rel
% 1.01/1.03  --clausifier_options                    --mode clausify
% 1.01/1.03  --stdin                                 false
% 1.01/1.03  --stats_out                             all
% 1.01/1.03  
% 1.01/1.03  ------ General Options
% 1.01/1.03  
% 1.01/1.03  --fof                                   false
% 1.01/1.03  --time_out_real                         305.
% 1.01/1.03  --time_out_virtual                      -1.
% 1.01/1.03  --symbol_type_check                     false
% 1.01/1.03  --clausify_out                          false
% 1.01/1.03  --sig_cnt_out                           false
% 1.01/1.03  --trig_cnt_out                          false
% 1.01/1.03  --trig_cnt_out_tolerance                1.
% 1.01/1.03  --trig_cnt_out_sk_spl                   false
% 1.01/1.03  --abstr_cl_out                          false
% 1.01/1.03  
% 1.01/1.03  ------ Global Options
% 1.01/1.03  
% 1.01/1.03  --schedule                              default
% 1.01/1.03  --add_important_lit                     false
% 1.01/1.03  --prop_solver_per_cl                    1000
% 1.01/1.03  --min_unsat_core                        false
% 1.01/1.03  --soft_assumptions                      false
% 1.01/1.03  --soft_lemma_size                       3
% 1.01/1.03  --prop_impl_unit_size                   0
% 1.01/1.03  --prop_impl_unit                        []
% 1.01/1.03  --share_sel_clauses                     true
% 1.01/1.03  --reset_solvers                         false
% 1.01/1.03  --bc_imp_inh                            [conj_cone]
% 1.01/1.03  --conj_cone_tolerance                   3.
% 1.01/1.03  --extra_neg_conj                        none
% 1.01/1.03  --large_theory_mode                     true
% 1.01/1.03  --prolific_symb_bound                   200
% 1.01/1.03  --lt_threshold                          2000
% 1.01/1.03  --clause_weak_htbl                      true
% 1.01/1.03  --gc_record_bc_elim                     false
% 1.01/1.03  
% 1.01/1.03  ------ Preprocessing Options
% 1.01/1.03  
% 1.01/1.03  --preprocessing_flag                    true
% 1.01/1.03  --time_out_prep_mult                    0.1
% 1.01/1.03  --splitting_mode                        input
% 1.01/1.03  --splitting_grd                         true
% 1.01/1.03  --splitting_cvd                         false
% 1.01/1.03  --splitting_cvd_svl                     false
% 1.01/1.03  --splitting_nvd                         32
% 1.01/1.03  --sub_typing                            true
% 1.01/1.03  --prep_gs_sim                           true
% 1.01/1.03  --prep_unflatten                        true
% 1.01/1.03  --prep_res_sim                          true
% 1.01/1.03  --prep_upred                            true
% 1.01/1.03  --prep_sem_filter                       exhaustive
% 1.01/1.03  --prep_sem_filter_out                   false
% 1.01/1.03  --pred_elim                             true
% 1.01/1.03  --res_sim_input                         true
% 1.01/1.03  --eq_ax_congr_red                       true
% 1.01/1.03  --pure_diseq_elim                       true
% 1.01/1.03  --brand_transform                       false
% 1.01/1.03  --non_eq_to_eq                          false
% 1.01/1.03  --prep_def_merge                        true
% 1.01/1.03  --prep_def_merge_prop_impl              false
% 1.01/1.03  --prep_def_merge_mbd                    true
% 1.01/1.03  --prep_def_merge_tr_red                 false
% 1.01/1.03  --prep_def_merge_tr_cl                  false
% 1.01/1.03  --smt_preprocessing                     true
% 1.01/1.03  --smt_ac_axioms                         fast
% 1.01/1.03  --preprocessed_out                      false
% 1.01/1.03  --preprocessed_stats                    false
% 1.01/1.03  
% 1.01/1.03  ------ Abstraction refinement Options
% 1.01/1.03  
% 1.01/1.03  --abstr_ref                             []
% 1.01/1.03  --abstr_ref_prep                        false
% 1.01/1.03  --abstr_ref_until_sat                   false
% 1.01/1.03  --abstr_ref_sig_restrict                funpre
% 1.01/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.01/1.03  --abstr_ref_under                       []
% 1.01/1.03  
% 1.01/1.03  ------ SAT Options
% 1.01/1.03  
% 1.01/1.03  --sat_mode                              false
% 1.01/1.03  --sat_fm_restart_options                ""
% 1.01/1.03  --sat_gr_def                            false
% 1.01/1.03  --sat_epr_types                         true
% 1.01/1.03  --sat_non_cyclic_types                  false
% 1.01/1.03  --sat_finite_models                     false
% 1.01/1.03  --sat_fm_lemmas                         false
% 1.01/1.03  --sat_fm_prep                           false
% 1.01/1.03  --sat_fm_uc_incr                        true
% 1.01/1.03  --sat_out_model                         small
% 1.01/1.03  --sat_out_clauses                       false
% 1.01/1.03  
% 1.01/1.03  ------ QBF Options
% 1.01/1.03  
% 1.01/1.03  --qbf_mode                              false
% 1.01/1.03  --qbf_elim_univ                         false
% 1.01/1.03  --qbf_dom_inst                          none
% 1.01/1.03  --qbf_dom_pre_inst                      false
% 1.01/1.03  --qbf_sk_in                             false
% 1.01/1.03  --qbf_pred_elim                         true
% 1.01/1.03  --qbf_split                             512
% 1.01/1.03  
% 1.01/1.03  ------ BMC1 Options
% 1.01/1.03  
% 1.01/1.03  --bmc1_incremental                      false
% 1.01/1.03  --bmc1_axioms                           reachable_all
% 1.01/1.03  --bmc1_min_bound                        0
% 1.01/1.03  --bmc1_max_bound                        -1
% 1.01/1.03  --bmc1_max_bound_default                -1
% 1.01/1.03  --bmc1_symbol_reachability              true
% 1.01/1.03  --bmc1_property_lemmas                  false
% 1.01/1.03  --bmc1_k_induction                      false
% 1.01/1.03  --bmc1_non_equiv_states                 false
% 1.01/1.03  --bmc1_deadlock                         false
% 1.01/1.03  --bmc1_ucm                              false
% 1.01/1.03  --bmc1_add_unsat_core                   none
% 1.01/1.03  --bmc1_unsat_core_children              false
% 1.01/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.01/1.03  --bmc1_out_stat                         full
% 1.01/1.03  --bmc1_ground_init                      false
% 1.01/1.03  --bmc1_pre_inst_next_state              false
% 1.01/1.03  --bmc1_pre_inst_state                   false
% 1.01/1.03  --bmc1_pre_inst_reach_state             false
% 1.01/1.03  --bmc1_out_unsat_core                   false
% 1.01/1.03  --bmc1_aig_witness_out                  false
% 1.01/1.03  --bmc1_verbose                          false
% 1.01/1.03  --bmc1_dump_clauses_tptp                false
% 1.01/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.01/1.03  --bmc1_dump_file                        -
% 1.01/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.01/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.01/1.03  --bmc1_ucm_extend_mode                  1
% 1.01/1.03  --bmc1_ucm_init_mode                    2
% 1.01/1.03  --bmc1_ucm_cone_mode                    none
% 1.01/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.01/1.03  --bmc1_ucm_relax_model                  4
% 1.01/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.01/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.01/1.03  --bmc1_ucm_layered_model                none
% 1.01/1.03  --bmc1_ucm_max_lemma_size               10
% 1.01/1.03  
% 1.01/1.03  ------ AIG Options
% 1.01/1.03  
% 1.01/1.03  --aig_mode                              false
% 1.01/1.03  
% 1.01/1.03  ------ Instantiation Options
% 1.01/1.03  
% 1.01/1.03  --instantiation_flag                    true
% 1.01/1.03  --inst_sos_flag                         false
% 1.01/1.03  --inst_sos_phase                        true
% 1.01/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.01/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.01/1.03  --inst_lit_sel_side                     num_symb
% 1.01/1.03  --inst_solver_per_active                1400
% 1.01/1.03  --inst_solver_calls_frac                1.
% 1.01/1.03  --inst_passive_queue_type               priority_queues
% 1.01/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.01/1.03  --inst_passive_queues_freq              [25;2]
% 1.01/1.03  --inst_dismatching                      true
% 1.01/1.03  --inst_eager_unprocessed_to_passive     true
% 1.01/1.03  --inst_prop_sim_given                   true
% 1.01/1.03  --inst_prop_sim_new                     false
% 1.01/1.03  --inst_subs_new                         false
% 1.01/1.03  --inst_eq_res_simp                      false
% 1.01/1.03  --inst_subs_given                       false
% 1.01/1.03  --inst_orphan_elimination               true
% 1.01/1.03  --inst_learning_loop_flag               true
% 1.01/1.03  --inst_learning_start                   3000
% 1.01/1.03  --inst_learning_factor                  2
% 1.01/1.03  --inst_start_prop_sim_after_learn       3
% 1.01/1.03  --inst_sel_renew                        solver
% 1.01/1.03  --inst_lit_activity_flag                true
% 1.01/1.03  --inst_restr_to_given                   false
% 1.01/1.03  --inst_activity_threshold               500
% 1.01/1.03  --inst_out_proof                        true
% 1.01/1.03  
% 1.01/1.03  ------ Resolution Options
% 1.01/1.03  
% 1.01/1.03  --resolution_flag                       true
% 1.01/1.03  --res_lit_sel                           adaptive
% 1.01/1.03  --res_lit_sel_side                      none
% 1.01/1.03  --res_ordering                          kbo
% 1.01/1.03  --res_to_prop_solver                    active
% 1.01/1.03  --res_prop_simpl_new                    false
% 1.01/1.03  --res_prop_simpl_given                  true
% 1.01/1.03  --res_passive_queue_type                priority_queues
% 1.01/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.01/1.03  --res_passive_queues_freq               [15;5]
% 1.01/1.03  --res_forward_subs                      full
% 1.01/1.03  --res_backward_subs                     full
% 1.01/1.03  --res_forward_subs_resolution           true
% 1.01/1.03  --res_backward_subs_resolution          true
% 1.01/1.03  --res_orphan_elimination                true
% 1.01/1.03  --res_time_limit                        2.
% 1.01/1.03  --res_out_proof                         true
% 1.01/1.03  
% 1.01/1.03  ------ Superposition Options
% 1.01/1.03  
% 1.01/1.03  --superposition_flag                    true
% 1.01/1.03  --sup_passive_queue_type                priority_queues
% 1.01/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.01/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.01/1.03  --demod_completeness_check              fast
% 1.01/1.03  --demod_use_ground                      true
% 1.01/1.03  --sup_to_prop_solver                    passive
% 1.01/1.03  --sup_prop_simpl_new                    true
% 1.01/1.03  --sup_prop_simpl_given                  true
% 1.01/1.03  --sup_fun_splitting                     false
% 1.01/1.03  --sup_smt_interval                      50000
% 1.01/1.03  
% 1.01/1.03  ------ Superposition Simplification Setup
% 1.01/1.03  
% 1.01/1.03  --sup_indices_passive                   []
% 1.01/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.01/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/1.03  --sup_full_bw                           [BwDemod]
% 1.01/1.03  --sup_immed_triv                        [TrivRules]
% 1.01/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.01/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/1.03  --sup_immed_bw_main                     []
% 1.01/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.01/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.01/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.01/1.03  
% 1.01/1.03  ------ Combination Options
% 1.01/1.03  
% 1.01/1.03  --comb_res_mult                         3
% 1.01/1.03  --comb_sup_mult                         2
% 1.01/1.03  --comb_inst_mult                        10
% 1.01/1.03  
% 1.01/1.03  ------ Debug Options
% 1.01/1.03  
% 1.01/1.03  --dbg_backtrace                         false
% 1.01/1.03  --dbg_dump_prop_clauses                 false
% 1.01/1.03  --dbg_dump_prop_clauses_file            -
% 1.01/1.03  --dbg_out_stat                          false
% 1.01/1.03  ------ Parsing...
% 1.01/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.01/1.03  
% 1.01/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.01/1.03  
% 1.01/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.01/1.03  
% 1.01/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.01/1.03  ------ Proving...
% 1.01/1.03  ------ Problem Properties 
% 1.01/1.03  
% 1.01/1.03  
% 1.01/1.03  clauses                                 11
% 1.01/1.03  conjectures                             2
% 1.01/1.03  EPR                                     0
% 1.01/1.03  Horn                                    11
% 1.01/1.03  unary                                   3
% 1.01/1.03  binary                                  2
% 1.01/1.03  lits                                    25
% 1.01/1.03  lits eq                                 9
% 1.01/1.03  fd_pure                                 0
% 1.01/1.03  fd_pseudo                               0
% 1.01/1.03  fd_cond                                 0
% 1.01/1.03  fd_pseudo_cond                          0
% 1.01/1.03  AC symbols                              0
% 1.01/1.03  
% 1.01/1.03  ------ Schedule dynamic 5 is on 
% 1.01/1.03  
% 1.01/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.01/1.03  
% 1.01/1.03  
% 1.01/1.03  ------ 
% 1.01/1.03  Current options:
% 1.01/1.03  ------ 
% 1.01/1.03  
% 1.01/1.03  ------ Input Options
% 1.01/1.03  
% 1.01/1.03  --out_options                           all
% 1.01/1.03  --tptp_safe_out                         true
% 1.01/1.03  --problem_path                          ""
% 1.01/1.03  --include_path                          ""
% 1.01/1.03  --clausifier                            res/vclausify_rel
% 1.01/1.03  --clausifier_options                    --mode clausify
% 1.01/1.03  --stdin                                 false
% 1.01/1.03  --stats_out                             all
% 1.01/1.03  
% 1.01/1.03  ------ General Options
% 1.01/1.03  
% 1.01/1.03  --fof                                   false
% 1.01/1.03  --time_out_real                         305.
% 1.01/1.03  --time_out_virtual                      -1.
% 1.01/1.03  --symbol_type_check                     false
% 1.01/1.03  --clausify_out                          false
% 1.01/1.03  --sig_cnt_out                           false
% 1.01/1.03  --trig_cnt_out                          false
% 1.01/1.03  --trig_cnt_out_tolerance                1.
% 1.01/1.03  --trig_cnt_out_sk_spl                   false
% 1.01/1.03  --abstr_cl_out                          false
% 1.01/1.03  
% 1.01/1.03  ------ Global Options
% 1.01/1.03  
% 1.01/1.03  --schedule                              default
% 1.01/1.03  --add_important_lit                     false
% 1.01/1.03  --prop_solver_per_cl                    1000
% 1.01/1.03  --min_unsat_core                        false
% 1.01/1.03  --soft_assumptions                      false
% 1.01/1.03  --soft_lemma_size                       3
% 1.01/1.03  --prop_impl_unit_size                   0
% 1.01/1.03  --prop_impl_unit                        []
% 1.01/1.03  --share_sel_clauses                     true
% 1.01/1.03  --reset_solvers                         false
% 1.01/1.03  --bc_imp_inh                            [conj_cone]
% 1.01/1.03  --conj_cone_tolerance                   3.
% 1.01/1.03  --extra_neg_conj                        none
% 1.01/1.03  --large_theory_mode                     true
% 1.01/1.03  --prolific_symb_bound                   200
% 1.01/1.03  --lt_threshold                          2000
% 1.01/1.03  --clause_weak_htbl                      true
% 1.01/1.03  --gc_record_bc_elim                     false
% 1.01/1.03  
% 1.01/1.03  ------ Preprocessing Options
% 1.01/1.03  
% 1.01/1.03  --preprocessing_flag                    true
% 1.01/1.03  --time_out_prep_mult                    0.1
% 1.01/1.03  --splitting_mode                        input
% 1.01/1.03  --splitting_grd                         true
% 1.01/1.03  --splitting_cvd                         false
% 1.01/1.03  --splitting_cvd_svl                     false
% 1.01/1.03  --splitting_nvd                         32
% 1.01/1.03  --sub_typing                            true
% 1.01/1.03  --prep_gs_sim                           true
% 1.01/1.03  --prep_unflatten                        true
% 1.01/1.03  --prep_res_sim                          true
% 1.01/1.03  --prep_upred                            true
% 1.01/1.03  --prep_sem_filter                       exhaustive
% 1.01/1.03  --prep_sem_filter_out                   false
% 1.01/1.03  --pred_elim                             true
% 1.01/1.03  --res_sim_input                         true
% 1.01/1.03  --eq_ax_congr_red                       true
% 1.01/1.03  --pure_diseq_elim                       true
% 1.01/1.03  --brand_transform                       false
% 1.01/1.03  --non_eq_to_eq                          false
% 1.01/1.03  --prep_def_merge                        true
% 1.01/1.03  --prep_def_merge_prop_impl              false
% 1.01/1.03  --prep_def_merge_mbd                    true
% 1.01/1.03  --prep_def_merge_tr_red                 false
% 1.01/1.03  --prep_def_merge_tr_cl                  false
% 1.01/1.03  --smt_preprocessing                     true
% 1.01/1.03  --smt_ac_axioms                         fast
% 1.01/1.03  --preprocessed_out                      false
% 1.01/1.03  --preprocessed_stats                    false
% 1.01/1.03  
% 1.01/1.03  ------ Abstraction refinement Options
% 1.01/1.03  
% 1.01/1.03  --abstr_ref                             []
% 1.01/1.03  --abstr_ref_prep                        false
% 1.01/1.03  --abstr_ref_until_sat                   false
% 1.01/1.03  --abstr_ref_sig_restrict                funpre
% 1.01/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.01/1.03  --abstr_ref_under                       []
% 1.01/1.03  
% 1.01/1.03  ------ SAT Options
% 1.01/1.03  
% 1.01/1.03  --sat_mode                              false
% 1.01/1.03  --sat_fm_restart_options                ""
% 1.01/1.03  --sat_gr_def                            false
% 1.01/1.03  --sat_epr_types                         true
% 1.01/1.03  --sat_non_cyclic_types                  false
% 1.01/1.03  --sat_finite_models                     false
% 1.01/1.03  --sat_fm_lemmas                         false
% 1.01/1.03  --sat_fm_prep                           false
% 1.01/1.03  --sat_fm_uc_incr                        true
% 1.01/1.03  --sat_out_model                         small
% 1.01/1.03  --sat_out_clauses                       false
% 1.01/1.03  
% 1.01/1.03  ------ QBF Options
% 1.01/1.03  
% 1.01/1.03  --qbf_mode                              false
% 1.01/1.03  --qbf_elim_univ                         false
% 1.01/1.03  --qbf_dom_inst                          none
% 1.01/1.03  --qbf_dom_pre_inst                      false
% 1.01/1.03  --qbf_sk_in                             false
% 1.01/1.03  --qbf_pred_elim                         true
% 1.01/1.03  --qbf_split                             512
% 1.01/1.03  
% 1.01/1.03  ------ BMC1 Options
% 1.01/1.03  
% 1.01/1.03  --bmc1_incremental                      false
% 1.01/1.03  --bmc1_axioms                           reachable_all
% 1.01/1.03  --bmc1_min_bound                        0
% 1.01/1.03  --bmc1_max_bound                        -1
% 1.01/1.03  --bmc1_max_bound_default                -1
% 1.01/1.03  --bmc1_symbol_reachability              true
% 1.01/1.03  --bmc1_property_lemmas                  false
% 1.01/1.03  --bmc1_k_induction                      false
% 1.01/1.03  --bmc1_non_equiv_states                 false
% 1.01/1.03  --bmc1_deadlock                         false
% 1.01/1.03  --bmc1_ucm                              false
% 1.01/1.03  --bmc1_add_unsat_core                   none
% 1.01/1.03  --bmc1_unsat_core_children              false
% 1.01/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.01/1.03  --bmc1_out_stat                         full
% 1.01/1.03  --bmc1_ground_init                      false
% 1.01/1.03  --bmc1_pre_inst_next_state              false
% 1.01/1.03  --bmc1_pre_inst_state                   false
% 1.01/1.03  --bmc1_pre_inst_reach_state             false
% 1.01/1.03  --bmc1_out_unsat_core                   false
% 1.01/1.03  --bmc1_aig_witness_out                  false
% 1.01/1.03  --bmc1_verbose                          false
% 1.01/1.03  --bmc1_dump_clauses_tptp                false
% 1.01/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.01/1.03  --bmc1_dump_file                        -
% 1.01/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.01/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.01/1.03  --bmc1_ucm_extend_mode                  1
% 1.01/1.03  --bmc1_ucm_init_mode                    2
% 1.01/1.03  --bmc1_ucm_cone_mode                    none
% 1.01/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.01/1.03  --bmc1_ucm_relax_model                  4
% 1.01/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.01/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.01/1.03  --bmc1_ucm_layered_model                none
% 1.01/1.03  --bmc1_ucm_max_lemma_size               10
% 1.01/1.03  
% 1.01/1.03  ------ AIG Options
% 1.01/1.03  
% 1.01/1.03  --aig_mode                              false
% 1.01/1.03  
% 1.01/1.03  ------ Instantiation Options
% 1.01/1.03  
% 1.01/1.03  --instantiation_flag                    true
% 1.01/1.03  --inst_sos_flag                         false
% 1.01/1.03  --inst_sos_phase                        true
% 1.01/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.01/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.01/1.03  --inst_lit_sel_side                     none
% 1.01/1.03  --inst_solver_per_active                1400
% 1.01/1.03  --inst_solver_calls_frac                1.
% 1.01/1.03  --inst_passive_queue_type               priority_queues
% 1.01/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.01/1.03  --inst_passive_queues_freq              [25;2]
% 1.01/1.03  --inst_dismatching                      true
% 1.01/1.03  --inst_eager_unprocessed_to_passive     true
% 1.01/1.03  --inst_prop_sim_given                   true
% 1.01/1.03  --inst_prop_sim_new                     false
% 1.01/1.03  --inst_subs_new                         false
% 1.01/1.03  --inst_eq_res_simp                      false
% 1.01/1.03  --inst_subs_given                       false
% 1.01/1.03  --inst_orphan_elimination               true
% 1.01/1.03  --inst_learning_loop_flag               true
% 1.01/1.03  --inst_learning_start                   3000
% 1.01/1.03  --inst_learning_factor                  2
% 1.01/1.03  --inst_start_prop_sim_after_learn       3
% 1.01/1.03  --inst_sel_renew                        solver
% 1.01/1.03  --inst_lit_activity_flag                true
% 1.01/1.03  --inst_restr_to_given                   false
% 1.01/1.03  --inst_activity_threshold               500
% 1.01/1.03  --inst_out_proof                        true
% 1.01/1.03  
% 1.01/1.03  ------ Resolution Options
% 1.01/1.03  
% 1.01/1.03  --resolution_flag                       false
% 1.01/1.03  --res_lit_sel                           adaptive
% 1.01/1.03  --res_lit_sel_side                      none
% 1.01/1.03  --res_ordering                          kbo
% 1.01/1.03  --res_to_prop_solver                    active
% 1.01/1.03  --res_prop_simpl_new                    false
% 1.01/1.03  --res_prop_simpl_given                  true
% 1.01/1.03  --res_passive_queue_type                priority_queues
% 1.01/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.01/1.03  --res_passive_queues_freq               [15;5]
% 1.01/1.03  --res_forward_subs                      full
% 1.01/1.03  --res_backward_subs                     full
% 1.01/1.03  --res_forward_subs_resolution           true
% 1.01/1.03  --res_backward_subs_resolution          true
% 1.01/1.03  --res_orphan_elimination                true
% 1.01/1.03  --res_time_limit                        2.
% 1.01/1.03  --res_out_proof                         true
% 1.01/1.03  
% 1.01/1.03  ------ Superposition Options
% 1.01/1.03  
% 1.01/1.03  --superposition_flag                    true
% 1.01/1.03  --sup_passive_queue_type                priority_queues
% 1.01/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.01/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.01/1.03  --demod_completeness_check              fast
% 1.01/1.03  --demod_use_ground                      true
% 1.01/1.03  --sup_to_prop_solver                    passive
% 1.01/1.03  --sup_prop_simpl_new                    true
% 1.01/1.03  --sup_prop_simpl_given                  true
% 1.01/1.03  --sup_fun_splitting                     false
% 1.01/1.03  --sup_smt_interval                      50000
% 1.01/1.03  
% 1.01/1.03  ------ Superposition Simplification Setup
% 1.01/1.03  
% 1.01/1.03  --sup_indices_passive                   []
% 1.01/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.01/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/1.03  --sup_full_bw                           [BwDemod]
% 1.01/1.03  --sup_immed_triv                        [TrivRules]
% 1.01/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.01/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/1.03  --sup_immed_bw_main                     []
% 1.01/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.01/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.01/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.01/1.03  
% 1.01/1.03  ------ Combination Options
% 1.01/1.03  
% 1.01/1.03  --comb_res_mult                         3
% 1.01/1.03  --comb_sup_mult                         2
% 1.01/1.03  --comb_inst_mult                        10
% 1.01/1.03  
% 1.01/1.03  ------ Debug Options
% 1.01/1.03  
% 1.01/1.03  --dbg_backtrace                         false
% 1.01/1.03  --dbg_dump_prop_clauses                 false
% 1.01/1.03  --dbg_dump_prop_clauses_file            -
% 1.01/1.03  --dbg_out_stat                          false
% 1.01/1.03  
% 1.01/1.03  
% 1.01/1.03  
% 1.01/1.03  
% 1.01/1.03  ------ Proving...
% 1.01/1.03  
% 1.01/1.03  
% 1.01/1.03  % SZS status Theorem for theBenchmark.p
% 1.01/1.03  
% 1.01/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 1.01/1.03  
% 1.01/1.03  fof(f11,conjecture,(
% 1.01/1.03    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 1.01/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f12,negated_conjecture,(
% 1.01/1.03    ~! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 1.01/1.03    inference(negated_conjecture,[],[f11])).
% 1.01/1.03  
% 1.01/1.03  fof(f34,plain,(
% 1.01/1.03    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.01/1.03    inference(ennf_transformation,[],[f12])).
% 1.01/1.03  
% 1.01/1.03  fof(f35,plain,(
% 1.01/1.03    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.01/1.03    inference(flattening,[],[f34])).
% 1.01/1.03  
% 1.01/1.03  fof(f45,plain,(
% 1.01/1.03    ( ! [X0,X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (~r3_lattices(X0,k7_lattices(X0,sK4),k7_lattices(X0,X1)) & r3_lattices(X0,X1,sK4) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 1.01/1.03    introduced(choice_axiom,[])).
% 1.01/1.03  
% 1.01/1.03  fof(f44,plain,(
% 1.01/1.03    ( ! [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,sK3)) & r3_lattices(X0,sK3,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 1.01/1.03    introduced(choice_axiom,[])).
% 1.01/1.03  
% 1.01/1.03  fof(f43,plain,(
% 1.01/1.03    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r3_lattices(sK2,k7_lattices(sK2,X2),k7_lattices(sK2,X1)) & r3_lattices(sK2,X1,X2) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l3_lattices(sK2) & v17_lattices(sK2) & v10_lattices(sK2) & ~v2_struct_0(sK2))),
% 1.01/1.03    introduced(choice_axiom,[])).
% 1.01/1.03  
% 1.01/1.03  fof(f46,plain,(
% 1.01/1.03    ((~r3_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) & r3_lattices(sK2,sK3,sK4) & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l3_lattices(sK2) & v17_lattices(sK2) & v10_lattices(sK2) & ~v2_struct_0(sK2)),
% 1.01/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f35,f45,f44,f43])).
% 1.01/1.03  
% 1.01/1.03  fof(f71,plain,(
% 1.01/1.03    m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.01/1.03    inference(cnf_transformation,[],[f46])).
% 1.01/1.03  
% 1.01/1.03  fof(f4,axiom,(
% 1.01/1.03    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 1.01/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f21,plain,(
% 1.01/1.03    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.01/1.03    inference(ennf_transformation,[],[f4])).
% 1.01/1.03  
% 1.01/1.03  fof(f22,plain,(
% 1.01/1.03    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.01/1.03    inference(flattening,[],[f21])).
% 1.01/1.03  
% 1.01/1.03  fof(f57,plain,(
% 1.01/1.03    ( ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/1.03    inference(cnf_transformation,[],[f22])).
% 1.01/1.03  
% 1.01/1.03  fof(f67,plain,(
% 1.01/1.03    ~v2_struct_0(sK2)),
% 1.01/1.03    inference(cnf_transformation,[],[f46])).
% 1.01/1.03  
% 1.01/1.03  fof(f70,plain,(
% 1.01/1.03    l3_lattices(sK2)),
% 1.01/1.03    inference(cnf_transformation,[],[f46])).
% 1.01/1.03  
% 1.01/1.03  fof(f72,plain,(
% 1.01/1.03    m1_subset_1(sK4,u1_struct_0(sK2))),
% 1.01/1.03    inference(cnf_transformation,[],[f46])).
% 1.01/1.03  
% 1.01/1.03  fof(f5,axiom,(
% 1.01/1.03    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 1.01/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f23,plain,(
% 1.01/1.03    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 1.01/1.03    inference(ennf_transformation,[],[f5])).
% 1.01/1.03  
% 1.01/1.03  fof(f58,plain,(
% 1.01/1.03    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 1.01/1.03    inference(cnf_transformation,[],[f23])).
% 1.01/1.03  
% 1.01/1.03  fof(f7,axiom,(
% 1.01/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2))),
% 1.01/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f26,plain,(
% 1.01/1.03    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.01/1.03    inference(ennf_transformation,[],[f7])).
% 1.01/1.03  
% 1.01/1.03  fof(f27,plain,(
% 1.01/1.03    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.01/1.03    inference(flattening,[],[f26])).
% 1.01/1.03  
% 1.01/1.03  fof(f61,plain,(
% 1.01/1.03    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/1.03    inference(cnf_transformation,[],[f27])).
% 1.01/1.03  
% 1.01/1.03  fof(f1,axiom,(
% 1.01/1.03    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.01/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f13,plain,(
% 1.01/1.03    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.01/1.03    inference(pure_predicate_removal,[],[f1])).
% 1.01/1.03  
% 1.01/1.03  fof(f14,plain,(
% 1.01/1.03    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.01/1.03    inference(pure_predicate_removal,[],[f13])).
% 1.01/1.03  
% 1.01/1.03  fof(f15,plain,(
% 1.01/1.03    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.01/1.03    inference(ennf_transformation,[],[f14])).
% 1.01/1.03  
% 1.01/1.03  fof(f16,plain,(
% 1.01/1.03    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.01/1.03    inference(flattening,[],[f15])).
% 1.01/1.03  
% 1.01/1.03  fof(f49,plain,(
% 1.01/1.03    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.01/1.03    inference(cnf_transformation,[],[f16])).
% 1.01/1.03  
% 1.01/1.03  fof(f68,plain,(
% 1.01/1.03    v10_lattices(sK2)),
% 1.01/1.03    inference(cnf_transformation,[],[f46])).
% 1.01/1.03  
% 1.01/1.03  fof(f2,axiom,(
% 1.01/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 1.01/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f17,plain,(
% 1.01/1.03    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 1.01/1.03    inference(ennf_transformation,[],[f2])).
% 1.01/1.03  
% 1.01/1.03  fof(f18,plain,(
% 1.01/1.03    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 1.01/1.03    inference(flattening,[],[f17])).
% 1.01/1.03  
% 1.01/1.03  fof(f52,plain,(
% 1.01/1.03    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/1.03    inference(cnf_transformation,[],[f18])).
% 1.01/1.03  
% 1.01/1.03  fof(f48,plain,(
% 1.01/1.03    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.01/1.03    inference(cnf_transformation,[],[f16])).
% 1.01/1.03  
% 1.01/1.03  fof(f59,plain,(
% 1.01/1.03    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 1.01/1.03    inference(cnf_transformation,[],[f23])).
% 1.01/1.03  
% 1.01/1.03  fof(f6,axiom,(
% 1.01/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 1.01/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f24,plain,(
% 1.01/1.03    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 1.01/1.03    inference(ennf_transformation,[],[f6])).
% 1.01/1.03  
% 1.01/1.03  fof(f25,plain,(
% 1.01/1.03    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 1.01/1.03    inference(flattening,[],[f24])).
% 1.01/1.03  
% 1.01/1.03  fof(f60,plain,(
% 1.01/1.03    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/1.03    inference(cnf_transformation,[],[f25])).
% 1.01/1.03  
% 1.01/1.03  fof(f3,axiom,(
% 1.01/1.03    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 1.01/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f19,plain,(
% 1.01/1.03    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.01/1.03    inference(ennf_transformation,[],[f3])).
% 1.01/1.03  
% 1.01/1.03  fof(f20,plain,(
% 1.01/1.03    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.01/1.03    inference(flattening,[],[f19])).
% 1.01/1.03  
% 1.01/1.03  fof(f36,plain,(
% 1.01/1.03    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.01/1.03    inference(nnf_transformation,[],[f20])).
% 1.01/1.03  
% 1.01/1.03  fof(f37,plain,(
% 1.01/1.03    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.01/1.03    inference(rectify,[],[f36])).
% 1.01/1.03  
% 1.01/1.03  fof(f39,plain,(
% 1.01/1.03    ( ! [X1] : (! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (k1_lattices(X0,k2_lattices(X0,X1,sK1(X0)),sK1(X0)) != sK1(X0) & m1_subset_1(sK1(X0),u1_struct_0(X0))))) )),
% 1.01/1.03    introduced(choice_axiom,[])).
% 1.01/1.03  
% 1.01/1.03  fof(f38,plain,(
% 1.01/1.03    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK0(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0))))),
% 1.01/1.03    introduced(choice_axiom,[])).
% 1.01/1.03  
% 1.01/1.03  fof(f40,plain,(
% 1.01/1.03    ! [X0] : (((v8_lattices(X0) | ((k1_lattices(X0,k2_lattices(X0,sK0(X0),sK1(X0)),sK1(X0)) != sK1(X0) & m1_subset_1(sK1(X0),u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.01/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).
% 1.01/1.03  
% 1.01/1.03  fof(f53,plain,(
% 1.01/1.03    ( ! [X4,X0,X3] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v8_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/1.03    inference(cnf_transformation,[],[f40])).
% 1.01/1.03  
% 1.01/1.03  fof(f50,plain,(
% 1.01/1.03    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.01/1.03    inference(cnf_transformation,[],[f16])).
% 1.01/1.03  
% 1.01/1.03  fof(f9,axiom,(
% 1.01/1.03    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 1.01/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f30,plain,(
% 1.01/1.03    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 1.01/1.03    inference(ennf_transformation,[],[f9])).
% 1.01/1.03  
% 1.01/1.03  fof(f31,plain,(
% 1.01/1.03    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.01/1.03    inference(flattening,[],[f30])).
% 1.01/1.03  
% 1.01/1.03  fof(f42,plain,(
% 1.01/1.03    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.01/1.03    inference(nnf_transformation,[],[f31])).
% 1.01/1.03  
% 1.01/1.03  fof(f64,plain,(
% 1.01/1.03    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/1.03    inference(cnf_transformation,[],[f42])).
% 1.01/1.03  
% 1.01/1.03  fof(f51,plain,(
% 1.01/1.03    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.01/1.03    inference(cnf_transformation,[],[f16])).
% 1.01/1.03  
% 1.01/1.03  fof(f73,plain,(
% 1.01/1.03    r3_lattices(sK2,sK3,sK4)),
% 1.01/1.03    inference(cnf_transformation,[],[f46])).
% 1.01/1.03  
% 1.01/1.03  fof(f8,axiom,(
% 1.01/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 1.01/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f28,plain,(
% 1.01/1.03    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.01/1.03    inference(ennf_transformation,[],[f8])).
% 1.01/1.03  
% 1.01/1.03  fof(f29,plain,(
% 1.01/1.03    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.01/1.03    inference(flattening,[],[f28])).
% 1.01/1.03  
% 1.01/1.03  fof(f41,plain,(
% 1.01/1.03    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.01/1.03    inference(nnf_transformation,[],[f29])).
% 1.01/1.03  
% 1.01/1.03  fof(f62,plain,(
% 1.01/1.03    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/1.03    inference(cnf_transformation,[],[f41])).
% 1.01/1.03  
% 1.01/1.03  fof(f10,axiom,(
% 1.01/1.03    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)))))),
% 1.01/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f32,plain,(
% 1.01/1.03    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.01/1.03    inference(ennf_transformation,[],[f10])).
% 1.01/1.03  
% 1.01/1.03  fof(f33,plain,(
% 1.01/1.03    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.01/1.03    inference(flattening,[],[f32])).
% 1.01/1.03  
% 1.01/1.03  fof(f66,plain,(
% 1.01/1.03    ( ! [X2,X0,X1] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/1.03    inference(cnf_transformation,[],[f33])).
% 1.01/1.03  
% 1.01/1.03  fof(f69,plain,(
% 1.01/1.03    v17_lattices(sK2)),
% 1.01/1.03    inference(cnf_transformation,[],[f46])).
% 1.01/1.03  
% 1.01/1.03  fof(f65,plain,(
% 1.01/1.03    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/1.03    inference(cnf_transformation,[],[f42])).
% 1.01/1.03  
% 1.01/1.03  fof(f74,plain,(
% 1.01/1.03    ~r3_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3))),
% 1.01/1.03    inference(cnf_transformation,[],[f46])).
% 1.01/1.03  
% 1.01/1.03  fof(f63,plain,(
% 1.01/1.03    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.01/1.03    inference(cnf_transformation,[],[f41])).
% 1.01/1.03  
% 1.01/1.03  cnf(c_23,negated_conjecture,
% 1.01/1.03      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.01/1.03      inference(cnf_transformation,[],[f71]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_799,negated_conjecture,
% 1.01/1.03      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.01/1.03      inference(subtyping,[status(esa)],[c_23]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_976,plain,
% 1.01/1.03      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 1.01/1.03      inference(predicate_to_equality,[status(thm)],[c_799]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_10,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.01/1.03      | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
% 1.01/1.03      | ~ l3_lattices(X1)
% 1.01/1.03      | v2_struct_0(X1) ),
% 1.01/1.03      inference(cnf_transformation,[],[f57]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_27,negated_conjecture,
% 1.01/1.03      ( ~ v2_struct_0(sK2) ),
% 1.01/1.03      inference(cnf_transformation,[],[f67]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_678,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.01/1.03      | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
% 1.01/1.03      | ~ l3_lattices(X1)
% 1.01/1.03      | sK2 != X1 ),
% 1.01/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_27]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_679,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.01/1.03      | m1_subset_1(k7_lattices(sK2,X0),u1_struct_0(sK2))
% 1.01/1.03      | ~ l3_lattices(sK2) ),
% 1.01/1.03      inference(unflattening,[status(thm)],[c_678]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_24,negated_conjecture,
% 1.01/1.03      ( l3_lattices(sK2) ),
% 1.01/1.03      inference(cnf_transformation,[],[f70]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_683,plain,
% 1.01/1.03      ( m1_subset_1(k7_lattices(sK2,X0),u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.01/1.03      inference(global_propositional_subsumption,
% 1.01/1.03                [status(thm)],
% 1.01/1.03                [c_679,c_24]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_684,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.01/1.03      | m1_subset_1(k7_lattices(sK2,X0),u1_struct_0(sK2)) ),
% 1.01/1.03      inference(renaming,[status(thm)],[c_683]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_792,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 1.01/1.03      | m1_subset_1(k7_lattices(sK2,X0_52),u1_struct_0(sK2)) ),
% 1.01/1.03      inference(subtyping,[status(esa)],[c_684]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_982,plain,
% 1.01/1.03      ( m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 1.01/1.03      | m1_subset_1(k7_lattices(sK2,X0_52),u1_struct_0(sK2)) = iProver_top ),
% 1.01/1.03      inference(predicate_to_equality,[status(thm)],[c_792]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_22,negated_conjecture,
% 1.01/1.03      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 1.01/1.03      inference(cnf_transformation,[],[f72]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_800,negated_conjecture,
% 1.01/1.03      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 1.01/1.03      inference(subtyping,[status(esa)],[c_22]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_975,plain,
% 1.01/1.03      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 1.01/1.03      inference(predicate_to_equality,[status(thm)],[c_800]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_12,plain,
% 1.01/1.03      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 1.01/1.03      inference(cnf_transformation,[],[f58]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_14,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.01/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.01/1.03      | ~ l1_lattices(X1)
% 1.01/1.03      | ~ v6_lattices(X1)
% 1.01/1.03      | v2_struct_0(X1)
% 1.01/1.03      | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0) ),
% 1.01/1.03      inference(cnf_transformation,[],[f61]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_301,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.01/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.01/1.03      | ~ v6_lattices(X1)
% 1.01/1.03      | ~ l3_lattices(X3)
% 1.01/1.03      | v2_struct_0(X1)
% 1.01/1.03      | X1 != X3
% 1.01/1.03      | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0) ),
% 1.01/1.03      inference(resolution_lifted,[status(thm)],[c_12,c_14]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_302,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.01/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.01/1.03      | ~ v6_lattices(X1)
% 1.01/1.03      | ~ l3_lattices(X1)
% 1.01/1.03      | v2_struct_0(X1)
% 1.01/1.03      | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0) ),
% 1.01/1.03      inference(unflattening,[status(thm)],[c_301]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_2,plain,
% 1.01/1.03      ( v6_lattices(X0)
% 1.01/1.03      | ~ l3_lattices(X0)
% 1.01/1.03      | v2_struct_0(X0)
% 1.01/1.03      | ~ v10_lattices(X0) ),
% 1.01/1.03      inference(cnf_transformation,[],[f49]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_26,negated_conjecture,
% 1.01/1.03      ( v10_lattices(sK2) ),
% 1.01/1.03      inference(cnf_transformation,[],[f68]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_368,plain,
% 1.01/1.03      ( v6_lattices(X0)
% 1.01/1.03      | ~ l3_lattices(X0)
% 1.01/1.03      | v2_struct_0(X0)
% 1.01/1.03      | sK2 != X0 ),
% 1.01/1.03      inference(resolution_lifted,[status(thm)],[c_2,c_26]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_369,plain,
% 1.01/1.03      ( v6_lattices(sK2) | ~ l3_lattices(sK2) | v2_struct_0(sK2) ),
% 1.01/1.03      inference(unflattening,[status(thm)],[c_368]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_86,plain,
% 1.01/1.03      ( v6_lattices(sK2)
% 1.01/1.03      | ~ l3_lattices(sK2)
% 1.01/1.03      | v2_struct_0(sK2)
% 1.01/1.03      | ~ v10_lattices(sK2) ),
% 1.01/1.03      inference(instantiation,[status(thm)],[c_2]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_371,plain,
% 1.01/1.03      ( v6_lattices(sK2) ),
% 1.01/1.03      inference(global_propositional_subsumption,
% 1.01/1.03                [status(thm)],
% 1.01/1.03                [c_369,c_27,c_26,c_24,c_86]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_507,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.01/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.01/1.03      | ~ l3_lattices(X1)
% 1.01/1.03      | v2_struct_0(X1)
% 1.01/1.03      | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0)
% 1.01/1.03      | sK2 != X1 ),
% 1.01/1.03      inference(resolution_lifted,[status(thm)],[c_302,c_371]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_508,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.01/1.03      | ~ l3_lattices(sK2)
% 1.01/1.03      | v2_struct_0(sK2)
% 1.01/1.03      | k4_lattices(sK2,X0,X1) = k2_lattices(sK2,X0,X1) ),
% 1.01/1.03      inference(unflattening,[status(thm)],[c_507]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_512,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.01/1.03      | k4_lattices(sK2,X0,X1) = k2_lattices(sK2,X0,X1) ),
% 1.01/1.03      inference(global_propositional_subsumption,
% 1.01/1.03                [status(thm)],
% 1.01/1.03                [c_508,c_27,c_24]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_795,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
% 1.01/1.03      | k4_lattices(sK2,X0_52,X1_52) = k2_lattices(sK2,X0_52,X1_52) ),
% 1.01/1.03      inference(subtyping,[status(esa)],[c_512]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_980,plain,
% 1.01/1.03      ( k4_lattices(sK2,X0_52,X1_52) = k2_lattices(sK2,X0_52,X1_52)
% 1.01/1.03      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 1.01/1.03      | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
% 1.01/1.03      inference(predicate_to_equality,[status(thm)],[c_795]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_2958,plain,
% 1.01/1.03      ( k4_lattices(sK2,k7_lattices(sK2,X0_52),X1_52) = k2_lattices(sK2,k7_lattices(sK2,X0_52),X1_52)
% 1.01/1.03      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 1.01/1.03      | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_982,c_980]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_8368,plain,
% 1.01/1.03      ( k4_lattices(sK2,k7_lattices(sK2,sK4),X0_52) = k2_lattices(sK2,k7_lattices(sK2,sK4),X0_52)
% 1.01/1.03      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_975,c_2958]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_8397,plain,
% 1.01/1.03      ( k4_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,X0_52)) = k2_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,X0_52))
% 1.01/1.03      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_982,c_8368]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_9033,plain,
% 1.01/1.03      ( k4_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) = k2_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_976,c_8397]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_5,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.01/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.01/1.03      | ~ l2_lattices(X1)
% 1.01/1.03      | ~ v4_lattices(X1)
% 1.01/1.03      | v2_struct_0(X1)
% 1.01/1.03      | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
% 1.01/1.03      inference(cnf_transformation,[],[f52]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_3,plain,
% 1.01/1.03      ( v4_lattices(X0)
% 1.01/1.03      | ~ l3_lattices(X0)
% 1.01/1.03      | v2_struct_0(X0)
% 1.01/1.03      | ~ v10_lattices(X0) ),
% 1.01/1.03      inference(cnf_transformation,[],[f48]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_357,plain,
% 1.01/1.03      ( v4_lattices(X0)
% 1.01/1.03      | ~ l3_lattices(X0)
% 1.01/1.03      | v2_struct_0(X0)
% 1.01/1.03      | sK2 != X0 ),
% 1.01/1.03      inference(resolution_lifted,[status(thm)],[c_3,c_26]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_358,plain,
% 1.01/1.03      ( v4_lattices(sK2) | ~ l3_lattices(sK2) | v2_struct_0(sK2) ),
% 1.01/1.03      inference(unflattening,[status(thm)],[c_357]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_83,plain,
% 1.01/1.03      ( v4_lattices(sK2)
% 1.01/1.03      | ~ l3_lattices(sK2)
% 1.01/1.03      | v2_struct_0(sK2)
% 1.01/1.03      | ~ v10_lattices(sK2) ),
% 1.01/1.03      inference(instantiation,[status(thm)],[c_3]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_360,plain,
% 1.01/1.03      ( v4_lattices(sK2) ),
% 1.01/1.03      inference(global_propositional_subsumption,
% 1.01/1.03                [status(thm)],
% 1.01/1.03                [c_358,c_27,c_26,c_24,c_83]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_430,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.01/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.01/1.03      | ~ l2_lattices(X1)
% 1.01/1.03      | v2_struct_0(X1)
% 1.01/1.03      | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
% 1.01/1.03      | sK2 != X1 ),
% 1.01/1.03      inference(resolution_lifted,[status(thm)],[c_5,c_360]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_431,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.01/1.03      | ~ l2_lattices(sK2)
% 1.01/1.03      | v2_struct_0(sK2)
% 1.01/1.03      | k3_lattices(sK2,X0,X1) = k3_lattices(sK2,X1,X0) ),
% 1.01/1.03      inference(unflattening,[status(thm)],[c_430]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_11,plain,
% 1.01/1.03      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 1.01/1.03      inference(cnf_transformation,[],[f59]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_61,plain,
% 1.01/1.03      ( l2_lattices(sK2) | ~ l3_lattices(sK2) ),
% 1.01/1.03      inference(instantiation,[status(thm)],[c_11]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_435,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.01/1.03      | k3_lattices(sK2,X0,X1) = k3_lattices(sK2,X1,X0) ),
% 1.01/1.03      inference(global_propositional_subsumption,
% 1.01/1.03                [status(thm)],
% 1.01/1.03                [c_431,c_27,c_24,c_61]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_796,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
% 1.01/1.03      | k3_lattices(sK2,X0_52,X1_52) = k3_lattices(sK2,X1_52,X0_52) ),
% 1.01/1.03      inference(subtyping,[status(esa)],[c_435]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_979,plain,
% 1.01/1.03      ( k3_lattices(sK2,X0_52,X1_52) = k3_lattices(sK2,X1_52,X0_52)
% 1.01/1.03      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 1.01/1.03      | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
% 1.01/1.03      inference(predicate_to_equality,[status(thm)],[c_796]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_2389,plain,
% 1.01/1.03      ( k3_lattices(sK2,X0_52,sK4) = k3_lattices(sK2,sK4,X0_52)
% 1.01/1.03      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_975,c_979]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_2510,plain,
% 1.01/1.03      ( k3_lattices(sK2,sK3,sK4) = k3_lattices(sK2,sK4,sK3) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_976,c_2389]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_13,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.01/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.01/1.03      | ~ l2_lattices(X1)
% 1.01/1.03      | ~ v4_lattices(X1)
% 1.01/1.03      | v2_struct_0(X1)
% 1.01/1.03      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
% 1.01/1.03      inference(cnf_transformation,[],[f60]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_409,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.01/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.01/1.03      | ~ l2_lattices(X1)
% 1.01/1.03      | v2_struct_0(X1)
% 1.01/1.03      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0)
% 1.01/1.03      | sK2 != X1 ),
% 1.01/1.03      inference(resolution_lifted,[status(thm)],[c_13,c_360]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_410,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.01/1.03      | ~ l2_lattices(sK2)
% 1.01/1.03      | v2_struct_0(sK2)
% 1.01/1.03      | k1_lattices(sK2,X0,X1) = k3_lattices(sK2,X0,X1) ),
% 1.01/1.03      inference(unflattening,[status(thm)],[c_409]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_414,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.01/1.03      | k1_lattices(sK2,X0,X1) = k3_lattices(sK2,X0,X1) ),
% 1.01/1.03      inference(global_propositional_subsumption,
% 1.01/1.03                [status(thm)],
% 1.01/1.03                [c_410,c_27,c_24,c_61]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_797,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
% 1.01/1.03      | k1_lattices(sK2,X0_52,X1_52) = k3_lattices(sK2,X0_52,X1_52) ),
% 1.01/1.03      inference(subtyping,[status(esa)],[c_414]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_978,plain,
% 1.01/1.03      ( k1_lattices(sK2,X0_52,X1_52) = k3_lattices(sK2,X0_52,X1_52)
% 1.01/1.03      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 1.01/1.03      | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
% 1.01/1.03      inference(predicate_to_equality,[status(thm)],[c_797]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_1784,plain,
% 1.01/1.03      ( k1_lattices(sK2,sK3,X0_52) = k3_lattices(sK2,sK3,X0_52)
% 1.01/1.03      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_976,c_978]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_2013,plain,
% 1.01/1.03      ( k1_lattices(sK2,sK3,sK4) = k3_lattices(sK2,sK3,sK4) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_975,c_1784]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_9,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.01/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.01/1.03      | ~ v8_lattices(X1)
% 1.01/1.03      | ~ l3_lattices(X1)
% 1.01/1.03      | v2_struct_0(X1)
% 1.01/1.03      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 ),
% 1.01/1.03      inference(cnf_transformation,[],[f53]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_696,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.01/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.01/1.03      | ~ v8_lattices(X1)
% 1.01/1.03      | ~ l3_lattices(X1)
% 1.01/1.03      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
% 1.01/1.03      | sK2 != X1 ),
% 1.01/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_27]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_697,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.01/1.03      | ~ v8_lattices(sK2)
% 1.01/1.03      | ~ l3_lattices(sK2)
% 1.01/1.03      | k1_lattices(sK2,k2_lattices(sK2,X0,X1),X1) = X1 ),
% 1.01/1.03      inference(unflattening,[status(thm)],[c_696]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_1,plain,
% 1.01/1.03      ( v8_lattices(X0)
% 1.01/1.03      | ~ l3_lattices(X0)
% 1.01/1.03      | v2_struct_0(X0)
% 1.01/1.03      | ~ v10_lattices(X0) ),
% 1.01/1.03      inference(cnf_transformation,[],[f50]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_89,plain,
% 1.01/1.03      ( v8_lattices(sK2)
% 1.01/1.03      | ~ l3_lattices(sK2)
% 1.01/1.03      | v2_struct_0(sK2)
% 1.01/1.03      | ~ v10_lattices(sK2) ),
% 1.01/1.03      inference(instantiation,[status(thm)],[c_1]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_701,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.01/1.03      | k1_lattices(sK2,k2_lattices(sK2,X0,X1),X1) = X1 ),
% 1.01/1.03      inference(global_propositional_subsumption,
% 1.01/1.03                [status(thm)],
% 1.01/1.03                [c_697,c_27,c_26,c_24,c_89]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_791,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
% 1.01/1.03      | k1_lattices(sK2,k2_lattices(sK2,X0_52,X1_52),X1_52) = X1_52 ),
% 1.01/1.03      inference(subtyping,[status(esa)],[c_701]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_983,plain,
% 1.01/1.03      ( k1_lattices(sK2,k2_lattices(sK2,X0_52,X1_52),X1_52) = X1_52
% 1.01/1.03      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 1.01/1.03      | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
% 1.01/1.03      inference(predicate_to_equality,[status(thm)],[c_791]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_1108,plain,
% 1.01/1.03      ( k1_lattices(sK2,k2_lattices(sK2,sK3,X0_52),X0_52) = X0_52
% 1.01/1.03      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_976,c_983]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_1390,plain,
% 1.01/1.03      ( k1_lattices(sK2,k2_lattices(sK2,sK3,sK4),sK4) = sK4 ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_975,c_1108]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_18,plain,
% 1.01/1.03      ( ~ r1_lattices(X0,X1,X2)
% 1.01/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.03      | ~ v8_lattices(X0)
% 1.01/1.03      | ~ l3_lattices(X0)
% 1.01/1.03      | v2_struct_0(X0)
% 1.01/1.03      | ~ v9_lattices(X0)
% 1.01/1.03      | k2_lattices(X0,X1,X2) = X1 ),
% 1.01/1.03      inference(cnf_transformation,[],[f64]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_0,plain,
% 1.01/1.03      ( ~ l3_lattices(X0)
% 1.01/1.03      | v2_struct_0(X0)
% 1.01/1.03      | ~ v10_lattices(X0)
% 1.01/1.03      | v9_lattices(X0) ),
% 1.01/1.03      inference(cnf_transformation,[],[f51]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_390,plain,
% 1.01/1.03      ( ~ l3_lattices(X0)
% 1.01/1.03      | v2_struct_0(X0)
% 1.01/1.03      | v9_lattices(X0)
% 1.01/1.03      | sK2 != X0 ),
% 1.01/1.03      inference(resolution_lifted,[status(thm)],[c_0,c_26]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_391,plain,
% 1.01/1.03      ( ~ l3_lattices(sK2) | v2_struct_0(sK2) | v9_lattices(sK2) ),
% 1.01/1.03      inference(unflattening,[status(thm)],[c_390]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_92,plain,
% 1.01/1.03      ( ~ l3_lattices(sK2)
% 1.01/1.03      | v2_struct_0(sK2)
% 1.01/1.03      | ~ v10_lattices(sK2)
% 1.01/1.03      | v9_lattices(sK2) ),
% 1.01/1.03      inference(instantiation,[status(thm)],[c_0]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_393,plain,
% 1.01/1.03      ( v9_lattices(sK2) ),
% 1.01/1.03      inference(global_propositional_subsumption,
% 1.01/1.03                [status(thm)],
% 1.01/1.03                [c_391,c_27,c_26,c_24,c_92]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_586,plain,
% 1.01/1.03      ( ~ r1_lattices(X0,X1,X2)
% 1.01/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.03      | ~ v8_lattices(X0)
% 1.01/1.03      | ~ l3_lattices(X0)
% 1.01/1.03      | v2_struct_0(X0)
% 1.01/1.03      | k2_lattices(X0,X1,X2) = X1
% 1.01/1.03      | sK2 != X0 ),
% 1.01/1.03      inference(resolution_lifted,[status(thm)],[c_18,c_393]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_587,plain,
% 1.01/1.03      ( ~ r1_lattices(sK2,X0,X1)
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.01/1.03      | ~ v8_lattices(sK2)
% 1.01/1.03      | ~ l3_lattices(sK2)
% 1.01/1.03      | v2_struct_0(sK2)
% 1.01/1.03      | k2_lattices(sK2,X0,X1) = X0 ),
% 1.01/1.03      inference(unflattening,[status(thm)],[c_586]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_591,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.01/1.03      | ~ r1_lattices(sK2,X0,X1)
% 1.01/1.03      | k2_lattices(sK2,X0,X1) = X0 ),
% 1.01/1.03      inference(global_propositional_subsumption,
% 1.01/1.03                [status(thm)],
% 1.01/1.03                [c_587,c_27,c_26,c_24,c_89]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_592,plain,
% 1.01/1.03      ( ~ r1_lattices(sK2,X0,X1)
% 1.01/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.01/1.03      | k2_lattices(sK2,X0,X1) = X0 ),
% 1.01/1.03      inference(renaming,[status(thm)],[c_591]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_21,negated_conjecture,
% 1.01/1.03      ( r3_lattices(sK2,sK3,sK4) ),
% 1.01/1.03      inference(cnf_transformation,[],[f73]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_16,plain,
% 1.01/1.03      ( r1_lattices(X0,X1,X2)
% 1.01/1.03      | ~ r3_lattices(X0,X1,X2)
% 1.01/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.03      | ~ v6_lattices(X0)
% 1.01/1.03      | ~ v8_lattices(X0)
% 1.01/1.03      | ~ l3_lattices(X0)
% 1.01/1.03      | v2_struct_0(X0)
% 1.01/1.03      | ~ v9_lattices(X0) ),
% 1.01/1.03      inference(cnf_transformation,[],[f62]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_459,plain,
% 1.01/1.03      ( r1_lattices(X0,X1,X2)
% 1.01/1.03      | ~ r3_lattices(X0,X1,X2)
% 1.01/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.03      | ~ v8_lattices(X0)
% 1.01/1.03      | ~ l3_lattices(X0)
% 1.01/1.03      | v2_struct_0(X0)
% 1.01/1.03      | ~ v9_lattices(X0)
% 1.01/1.03      | sK2 != X0 ),
% 1.01/1.03      inference(resolution_lifted,[status(thm)],[c_16,c_371]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_460,plain,
% 1.01/1.03      ( r1_lattices(sK2,X0,X1)
% 1.01/1.03      | ~ r3_lattices(sK2,X0,X1)
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.01/1.03      | ~ v8_lattices(sK2)
% 1.01/1.03      | ~ l3_lattices(sK2)
% 1.01/1.03      | v2_struct_0(sK2)
% 1.01/1.03      | ~ v9_lattices(sK2) ),
% 1.01/1.03      inference(unflattening,[status(thm)],[c_459]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_464,plain,
% 1.01/1.03      ( r1_lattices(sK2,X0,X1)
% 1.01/1.03      | ~ r3_lattices(sK2,X0,X1)
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.01/1.03      inference(global_propositional_subsumption,
% 1.01/1.03                [status(thm)],
% 1.01/1.03                [c_460,c_27,c_26,c_24,c_89,c_92]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_465,plain,
% 1.01/1.03      ( r1_lattices(sK2,X0,X1)
% 1.01/1.03      | ~ r3_lattices(sK2,X0,X1)
% 1.01/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.01/1.03      inference(renaming,[status(thm)],[c_464]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_566,plain,
% 1.01/1.03      ( r1_lattices(sK2,X0,X1)
% 1.01/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.01/1.03      | sK3 != X0
% 1.01/1.03      | sK4 != X1
% 1.01/1.03      | sK2 != sK2 ),
% 1.01/1.03      inference(resolution_lifted,[status(thm)],[c_21,c_465]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_567,plain,
% 1.01/1.03      ( r1_lattices(sK2,sK3,sK4)
% 1.01/1.03      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 1.01/1.03      inference(unflattening,[status(thm)],[c_566]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_569,plain,
% 1.01/1.03      ( r1_lattices(sK2,sK3,sK4) ),
% 1.01/1.03      inference(global_propositional_subsumption,
% 1.01/1.03                [status(thm)],
% 1.01/1.03                [c_567,c_23,c_22]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_658,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.01/1.03      | k2_lattices(sK2,X0,X1) = X0
% 1.01/1.03      | sK3 != X0
% 1.01/1.03      | sK4 != X1
% 1.01/1.03      | sK2 != sK2 ),
% 1.01/1.03      inference(resolution_lifted,[status(thm)],[c_592,c_569]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_659,plain,
% 1.01/1.03      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 1.01/1.03      | k2_lattices(sK2,sK3,sK4) = sK3 ),
% 1.01/1.03      inference(unflattening,[status(thm)],[c_658]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_661,plain,
% 1.01/1.03      ( k2_lattices(sK2,sK3,sK4) = sK3 ),
% 1.01/1.03      inference(global_propositional_subsumption,
% 1.01/1.03                [status(thm)],
% 1.01/1.03                [c_659,c_23,c_22]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_793,plain,
% 1.01/1.03      ( k2_lattices(sK2,sK3,sK4) = sK3 ),
% 1.01/1.03      inference(subtyping,[status(esa)],[c_661]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_1400,plain,
% 1.01/1.03      ( k1_lattices(sK2,sK3,sK4) = sK4 ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_1390,c_793]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_2023,plain,
% 1.01/1.03      ( k3_lattices(sK2,sK3,sK4) = sK4 ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_2013,c_1400]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_2517,plain,
% 1.01/1.03      ( k3_lattices(sK2,sK4,sK3) = sK4 ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_2510,c_2023]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_19,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.01/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.01/1.03      | ~ v17_lattices(X1)
% 1.01/1.03      | ~ l3_lattices(X1)
% 1.01/1.03      | v2_struct_0(X1)
% 1.01/1.03      | ~ v10_lattices(X1)
% 1.01/1.03      | k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k3_lattices(X1,X2,X0)) ),
% 1.01/1.03      inference(cnf_transformation,[],[f66]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_25,negated_conjecture,
% 1.01/1.03      ( v17_lattices(sK2) ),
% 1.01/1.03      inference(cnf_transformation,[],[f69]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_332,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.01/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.01/1.03      | ~ l3_lattices(X1)
% 1.01/1.03      | v2_struct_0(X1)
% 1.01/1.03      | ~ v10_lattices(X1)
% 1.01/1.03      | k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k3_lattices(X1,X2,X0))
% 1.01/1.03      | sK2 != X1 ),
% 1.01/1.03      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_333,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.01/1.03      | ~ l3_lattices(sK2)
% 1.01/1.03      | v2_struct_0(sK2)
% 1.01/1.03      | ~ v10_lattices(sK2)
% 1.01/1.03      | k4_lattices(sK2,k7_lattices(sK2,X0),k7_lattices(sK2,X1)) = k7_lattices(sK2,k3_lattices(sK2,X0,X1)) ),
% 1.01/1.03      inference(unflattening,[status(thm)],[c_332]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_337,plain,
% 1.01/1.03      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.01/1.03      | k4_lattices(sK2,k7_lattices(sK2,X0),k7_lattices(sK2,X1)) = k7_lattices(sK2,k3_lattices(sK2,X0,X1)) ),
% 1.01/1.03      inference(global_propositional_subsumption,
% 1.01/1.03                [status(thm)],
% 1.01/1.03                [c_333,c_27,c_26,c_24]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_338,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.01/1.03      | k4_lattices(sK2,k7_lattices(sK2,X0),k7_lattices(sK2,X1)) = k7_lattices(sK2,k3_lattices(sK2,X0,X1)) ),
% 1.01/1.03      inference(renaming,[status(thm)],[c_337]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_798,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
% 1.01/1.03      | k4_lattices(sK2,k7_lattices(sK2,X0_52),k7_lattices(sK2,X1_52)) = k7_lattices(sK2,k3_lattices(sK2,X0_52,X1_52)) ),
% 1.01/1.03      inference(subtyping,[status(esa)],[c_338]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_977,plain,
% 1.01/1.03      ( k4_lattices(sK2,k7_lattices(sK2,X0_52),k7_lattices(sK2,X1_52)) = k7_lattices(sK2,k3_lattices(sK2,X0_52,X1_52))
% 1.01/1.03      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 1.01/1.03      | m1_subset_1(X1_52,u1_struct_0(sK2)) != iProver_top ),
% 1.01/1.03      inference(predicate_to_equality,[status(thm)],[c_798]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_1245,plain,
% 1.01/1.03      ( k4_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,X0_52)) = k7_lattices(sK2,k3_lattices(sK2,sK4,X0_52))
% 1.01/1.03      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_975,c_977]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_1463,plain,
% 1.01/1.03      ( k4_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) = k7_lattices(sK2,k3_lattices(sK2,sK4,sK3)) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_976,c_1245]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_2682,plain,
% 1.01/1.03      ( k4_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) = k7_lattices(sK2,sK4) ),
% 1.01/1.03      inference(demodulation,[status(thm)],[c_2517,c_1463]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_9040,plain,
% 1.01/1.03      ( k2_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) = k7_lattices(sK2,sK4) ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_9033,c_2682]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_1053,plain,
% 1.01/1.03      ( m1_subset_1(k7_lattices(sK2,sK4),u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 1.01/1.03      inference(instantiation,[status(thm)],[c_792]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_832,plain,
% 1.01/1.03      ( m1_subset_1(k7_lattices(sK2,sK3),u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.01/1.03      inference(instantiation,[status(thm)],[c_792]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_17,plain,
% 1.01/1.03      ( r1_lattices(X0,X1,X2)
% 1.01/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.03      | ~ v8_lattices(X0)
% 1.01/1.03      | ~ l3_lattices(X0)
% 1.01/1.03      | v2_struct_0(X0)
% 1.01/1.03      | ~ v9_lattices(X0)
% 1.01/1.03      | k2_lattices(X0,X1,X2) != X1 ),
% 1.01/1.03      inference(cnf_transformation,[],[f65]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_610,plain,
% 1.01/1.03      ( r1_lattices(X0,X1,X2)
% 1.01/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.03      | ~ v8_lattices(X0)
% 1.01/1.03      | ~ l3_lattices(X0)
% 1.01/1.03      | v2_struct_0(X0)
% 1.01/1.03      | k2_lattices(X0,X1,X2) != X1
% 1.01/1.03      | sK2 != X0 ),
% 1.01/1.03      inference(resolution_lifted,[status(thm)],[c_17,c_393]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_611,plain,
% 1.01/1.03      ( r1_lattices(sK2,X0,X1)
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.01/1.03      | ~ v8_lattices(sK2)
% 1.01/1.03      | ~ l3_lattices(sK2)
% 1.01/1.03      | v2_struct_0(sK2)
% 1.01/1.03      | k2_lattices(sK2,X0,X1) != X0 ),
% 1.01/1.03      inference(unflattening,[status(thm)],[c_610]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_615,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.01/1.03      | r1_lattices(sK2,X0,X1)
% 1.01/1.03      | k2_lattices(sK2,X0,X1) != X0 ),
% 1.01/1.03      inference(global_propositional_subsumption,
% 1.01/1.03                [status(thm)],
% 1.01/1.03                [c_611,c_27,c_26,c_24,c_89]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_616,plain,
% 1.01/1.03      ( r1_lattices(sK2,X0,X1)
% 1.01/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.01/1.03      | k2_lattices(sK2,X0,X1) != X0 ),
% 1.01/1.03      inference(renaming,[status(thm)],[c_615]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_20,negated_conjecture,
% 1.01/1.03      ( ~ r3_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) ),
% 1.01/1.03      inference(cnf_transformation,[],[f74]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_15,plain,
% 1.01/1.03      ( ~ r1_lattices(X0,X1,X2)
% 1.01/1.03      | r3_lattices(X0,X1,X2)
% 1.01/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.03      | ~ v6_lattices(X0)
% 1.01/1.03      | ~ v8_lattices(X0)
% 1.01/1.03      | ~ l3_lattices(X0)
% 1.01/1.03      | v2_struct_0(X0)
% 1.01/1.03      | ~ v9_lattices(X0) ),
% 1.01/1.03      inference(cnf_transformation,[],[f63]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_483,plain,
% 1.01/1.03      ( ~ r1_lattices(X0,X1,X2)
% 1.01/1.03      | r3_lattices(X0,X1,X2)
% 1.01/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.01/1.03      | ~ v8_lattices(X0)
% 1.01/1.03      | ~ l3_lattices(X0)
% 1.01/1.03      | v2_struct_0(X0)
% 1.01/1.03      | ~ v9_lattices(X0)
% 1.01/1.03      | sK2 != X0 ),
% 1.01/1.03      inference(resolution_lifted,[status(thm)],[c_15,c_371]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_484,plain,
% 1.01/1.03      ( ~ r1_lattices(sK2,X0,X1)
% 1.01/1.03      | r3_lattices(sK2,X0,X1)
% 1.01/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.01/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.01/1.03      | ~ v8_lattices(sK2)
% 1.01/1.03      | ~ l3_lattices(sK2)
% 1.01/1.04      | v2_struct_0(sK2)
% 1.01/1.04      | ~ v9_lattices(sK2) ),
% 1.01/1.04      inference(unflattening,[status(thm)],[c_483]) ).
% 1.01/1.04  
% 1.01/1.04  cnf(c_488,plain,
% 1.01/1.04      ( ~ r1_lattices(sK2,X0,X1)
% 1.01/1.04      | r3_lattices(sK2,X0,X1)
% 1.01/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.01/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.01/1.04      inference(global_propositional_subsumption,
% 1.01/1.04                [status(thm)],
% 1.01/1.04                [c_484,c_27,c_26,c_24,c_89,c_92]) ).
% 1.01/1.04  
% 1.01/1.04  cnf(c_489,plain,
% 1.01/1.04      ( ~ r1_lattices(sK2,X0,X1)
% 1.01/1.04      | r3_lattices(sK2,X0,X1)
% 1.01/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.01/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.01/1.04      inference(renaming,[status(thm)],[c_488]) ).
% 1.01/1.04  
% 1.01/1.04  cnf(c_553,plain,
% 1.01/1.04      ( ~ r1_lattices(sK2,X0,X1)
% 1.01/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.01/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.01/1.04      | k7_lattices(sK2,sK3) != X1
% 1.01/1.04      | k7_lattices(sK2,sK4) != X0
% 1.01/1.04      | sK2 != sK2 ),
% 1.01/1.04      inference(resolution_lifted,[status(thm)],[c_20,c_489]) ).
% 1.01/1.04  
% 1.01/1.04  cnf(c_554,plain,
% 1.01/1.04      ( ~ r1_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3))
% 1.01/1.04      | ~ m1_subset_1(k7_lattices(sK2,sK3),u1_struct_0(sK2))
% 1.01/1.04      | ~ m1_subset_1(k7_lattices(sK2,sK4),u1_struct_0(sK2)) ),
% 1.01/1.04      inference(unflattening,[status(thm)],[c_553]) ).
% 1.01/1.04  
% 1.01/1.04  cnf(c_645,plain,
% 1.01/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.01/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.01/1.04      | ~ m1_subset_1(k7_lattices(sK2,sK3),u1_struct_0(sK2))
% 1.01/1.04      | ~ m1_subset_1(k7_lattices(sK2,sK4),u1_struct_0(sK2))
% 1.01/1.04      | k2_lattices(sK2,X0,X1) != X0
% 1.01/1.04      | k7_lattices(sK2,sK3) != X1
% 1.01/1.04      | k7_lattices(sK2,sK4) != X0
% 1.01/1.04      | sK2 != sK2 ),
% 1.01/1.04      inference(resolution_lifted,[status(thm)],[c_616,c_554]) ).
% 1.01/1.04  
% 1.01/1.04  cnf(c_646,plain,
% 1.01/1.04      ( ~ m1_subset_1(k7_lattices(sK2,sK3),u1_struct_0(sK2))
% 1.01/1.04      | ~ m1_subset_1(k7_lattices(sK2,sK4),u1_struct_0(sK2))
% 1.01/1.04      | k2_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) != k7_lattices(sK2,sK4) ),
% 1.01/1.04      inference(unflattening,[status(thm)],[c_645]) ).
% 1.01/1.04  
% 1.01/1.04  cnf(c_794,plain,
% 1.01/1.04      ( ~ m1_subset_1(k7_lattices(sK2,sK3),u1_struct_0(sK2))
% 1.01/1.04      | ~ m1_subset_1(k7_lattices(sK2,sK4),u1_struct_0(sK2))
% 1.01/1.04      | k2_lattices(sK2,k7_lattices(sK2,sK4),k7_lattices(sK2,sK3)) != k7_lattices(sK2,sK4) ),
% 1.01/1.04      inference(subtyping,[status(esa)],[c_646]) ).
% 1.01/1.04  
% 1.01/1.04  cnf(contradiction,plain,
% 1.01/1.04      ( $false ),
% 1.01/1.04      inference(minisat,
% 1.01/1.04                [status(thm)],
% 1.01/1.04                [c_9040,c_1053,c_832,c_794,c_22,c_23]) ).
% 1.01/1.04  
% 1.01/1.04  
% 1.01/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 1.01/1.04  
% 1.01/1.04  ------                               Statistics
% 1.01/1.04  
% 1.01/1.04  ------ General
% 1.01/1.04  
% 1.01/1.04  abstr_ref_over_cycles:                  0
% 1.01/1.04  abstr_ref_under_cycles:                 0
% 1.01/1.04  gc_basic_clause_elim:                   0
% 1.01/1.04  forced_gc_time:                         0
% 1.01/1.04  parsing_time:                           0.011
% 1.01/1.04  unif_index_cands_time:                  0.
% 1.01/1.04  unif_index_add_time:                    0.
% 1.01/1.04  orderings_time:                         0.
% 1.01/1.04  out_proof_time:                         0.014
% 1.01/1.04  total_time:                             0.338
% 1.01/1.04  num_of_symbols:                         55
% 1.01/1.04  num_of_terms:                           6943
% 1.01/1.04  
% 1.01/1.04  ------ Preprocessing
% 1.01/1.04  
% 1.01/1.04  num_of_splits:                          0
% 1.01/1.04  num_of_split_atoms:                     0
% 1.01/1.04  num_of_reused_defs:                     0
% 1.01/1.04  num_eq_ax_congr_red:                    30
% 1.01/1.04  num_of_sem_filtered_clauses:            1
% 1.01/1.04  num_of_subtypes:                        3
% 1.01/1.04  monotx_restored_types:                  0
% 1.01/1.04  sat_num_of_epr_types:                   0
% 1.01/1.04  sat_num_of_non_cyclic_types:            0
% 1.01/1.04  sat_guarded_non_collapsed_types:        1
% 1.01/1.04  num_pure_diseq_elim:                    0
% 1.01/1.04  simp_replaced_by:                       0
% 1.01/1.04  res_preprocessed:                       75
% 1.01/1.04  prep_upred:                             0
% 1.01/1.04  prep_unflattend:                        26
% 1.01/1.04  smt_new_axioms:                         0
% 1.01/1.04  pred_elim_cands:                        1
% 1.01/1.04  pred_elim:                              12
% 1.01/1.04  pred_elim_cl:                           16
% 1.01/1.04  pred_elim_cycles:                       14
% 1.01/1.04  merged_defs:                            0
% 1.01/1.04  merged_defs_ncl:                        0
% 1.01/1.04  bin_hyper_res:                          0
% 1.01/1.04  prep_cycles:                            4
% 1.01/1.04  pred_elim_time:                         0.01
% 1.01/1.04  splitting_time:                         0.
% 1.01/1.04  sem_filter_time:                        0.
% 1.01/1.04  monotx_time:                            0.
% 1.01/1.04  subtype_inf_time:                       0.
% 1.01/1.04  
% 1.01/1.04  ------ Problem properties
% 1.01/1.04  
% 1.01/1.04  clauses:                                11
% 1.01/1.04  conjectures:                            2
% 1.01/1.04  epr:                                    0
% 1.01/1.04  horn:                                   11
% 1.01/1.04  ground:                                 5
% 1.01/1.04  unary:                                  3
% 1.01/1.04  binary:                                 2
% 1.01/1.04  lits:                                   25
% 1.01/1.04  lits_eq:                                9
% 1.01/1.04  fd_pure:                                0
% 1.01/1.04  fd_pseudo:                              0
% 1.01/1.04  fd_cond:                                0
% 1.01/1.04  fd_pseudo_cond:                         0
% 1.01/1.04  ac_symbols:                             0
% 1.01/1.04  
% 1.01/1.04  ------ Propositional Solver
% 1.01/1.04  
% 1.01/1.04  prop_solver_calls:                      33
% 1.01/1.04  prop_fast_solver_calls:                 779
% 1.01/1.04  smt_solver_calls:                       0
% 1.01/1.04  smt_fast_solver_calls:                  0
% 1.01/1.04  prop_num_of_clauses:                    3258
% 1.01/1.04  prop_preprocess_simplified:             8086
% 1.01/1.04  prop_fo_subsumed:                       41
% 1.01/1.04  prop_solver_time:                       0.
% 1.01/1.04  smt_solver_time:                        0.
% 1.01/1.04  smt_fast_solver_time:                   0.
% 1.01/1.04  prop_fast_solver_time:                  0.
% 1.01/1.04  prop_unsat_core_time:                   0.
% 1.01/1.04  
% 1.01/1.04  ------ QBF
% 1.01/1.04  
% 1.01/1.04  qbf_q_res:                              0
% 1.01/1.04  qbf_num_tautologies:                    0
% 1.01/1.04  qbf_prep_cycles:                        0
% 1.01/1.04  
% 1.01/1.04  ------ BMC1
% 1.01/1.04  
% 1.01/1.04  bmc1_current_bound:                     -1
% 1.01/1.04  bmc1_last_solved_bound:                 -1
% 1.01/1.04  bmc1_unsat_core_size:                   -1
% 1.01/1.04  bmc1_unsat_core_parents_size:           -1
% 1.01/1.04  bmc1_merge_next_fun:                    0
% 1.01/1.04  bmc1_unsat_core_clauses_time:           0.
% 1.01/1.04  
% 1.01/1.04  ------ Instantiation
% 1.01/1.04  
% 1.01/1.04  inst_num_of_clauses:                    1448
% 1.01/1.04  inst_num_in_passive:                    750
% 1.01/1.04  inst_num_in_active:                     678
% 1.01/1.04  inst_num_in_unprocessed:                20
% 1.01/1.04  inst_num_of_loops:                      720
% 1.01/1.04  inst_num_of_learning_restarts:          0
% 1.01/1.04  inst_num_moves_active_passive:          35
% 1.01/1.04  inst_lit_activity:                      0
% 1.01/1.04  inst_lit_activity_moves:                0
% 1.01/1.04  inst_num_tautologies:                   0
% 1.01/1.04  inst_num_prop_implied:                  0
% 1.01/1.04  inst_num_existing_simplified:           0
% 1.01/1.04  inst_num_eq_res_simplified:             0
% 1.01/1.04  inst_num_child_elim:                    0
% 1.01/1.04  inst_num_of_dismatching_blockings:      849
% 1.01/1.04  inst_num_of_non_proper_insts:           2092
% 1.01/1.04  inst_num_of_duplicates:                 0
% 1.01/1.04  inst_inst_num_from_inst_to_res:         0
% 1.01/1.04  inst_dismatching_checking_time:         0.
% 1.01/1.04  
% 1.01/1.04  ------ Resolution
% 1.01/1.04  
% 1.01/1.04  res_num_of_clauses:                     0
% 1.01/1.04  res_num_in_passive:                     0
% 1.01/1.04  res_num_in_active:                      0
% 1.01/1.04  res_num_of_loops:                       79
% 1.01/1.04  res_forward_subset_subsumed:            186
% 1.01/1.04  res_backward_subset_subsumed:           0
% 1.01/1.04  res_forward_subsumed:                   0
% 1.01/1.04  res_backward_subsumed:                  0
% 1.01/1.04  res_forward_subsumption_resolution:     0
% 1.01/1.04  res_backward_subsumption_resolution:    0
% 1.01/1.04  res_clause_to_clause_subsumption:       418
% 1.01/1.04  res_orphan_elimination:                 0
% 1.01/1.04  res_tautology_del:                      144
% 1.01/1.04  res_num_eq_res_simplified:              1
% 1.01/1.04  res_num_sel_changes:                    0
% 1.01/1.04  res_moves_from_active_to_pass:          0
% 1.01/1.04  
% 1.01/1.04  ------ Superposition
% 1.01/1.04  
% 1.01/1.04  sup_time_total:                         0.
% 1.01/1.04  sup_time_generating:                    0.
% 1.01/1.04  sup_time_sim_full:                      0.
% 1.01/1.04  sup_time_sim_immed:                     0.
% 1.01/1.04  
% 1.01/1.04  sup_num_of_clauses:                     164
% 1.01/1.04  sup_num_in_active:                      140
% 1.01/1.04  sup_num_in_passive:                     24
% 1.01/1.04  sup_num_of_loops:                       142
% 1.01/1.04  sup_fw_superposition:                   159
% 1.01/1.04  sup_bw_superposition:                   0
% 1.01/1.04  sup_immediate_simplified:               14
% 1.01/1.04  sup_given_eliminated:                   0
% 1.01/1.04  comparisons_done:                       0
% 1.01/1.04  comparisons_avoided:                    0
% 1.01/1.04  
% 1.01/1.04  ------ Simplifications
% 1.01/1.04  
% 1.01/1.04  
% 1.01/1.04  sim_fw_subset_subsumed:                 0
% 1.01/1.04  sim_bw_subset_subsumed:                 0
% 1.01/1.04  sim_fw_subsumed:                        0
% 1.01/1.04  sim_bw_subsumed:                        0
% 1.01/1.04  sim_fw_subsumption_res:                 0
% 1.01/1.04  sim_bw_subsumption_res:                 0
% 1.01/1.04  sim_tautology_del:                      0
% 1.01/1.04  sim_eq_tautology_del:                   2
% 1.01/1.04  sim_eq_res_simp:                        0
% 1.01/1.04  sim_fw_demodulated:                     0
% 1.01/1.04  sim_bw_demodulated:                     3
% 1.01/1.04  sim_light_normalised:                   14
% 1.01/1.04  sim_joinable_taut:                      0
% 1.01/1.04  sim_joinable_simp:                      0
% 1.01/1.04  sim_ac_normalised:                      0
% 1.01/1.04  sim_smt_subsumption:                    0
% 1.01/1.04  
%------------------------------------------------------------------------------
