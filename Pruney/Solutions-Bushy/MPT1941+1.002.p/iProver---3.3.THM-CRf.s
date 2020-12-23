%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1941+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:54 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 537 expanded)
%              Number of clauses        :   97 ( 144 expanded)
%              Number of leaves         :   21 ( 146 expanded)
%              Depth                    :   17
%              Number of atoms          :  666 (4002 expanded)
%              Number of equality atoms :  178 ( 250 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = k2_yellow_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = k2_yellow_1(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f81,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f55,f52])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f50,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f54,plain,(
    ! [X0] : v1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f82,plain,(
    ! [X0] : v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f54,f52])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k1_yellow_1(X0),X0)
      & v8_relat_2(k1_yellow_1(X0))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v8_relat_2(k1_yellow_1(X0))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f17,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f19,plain,(
    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
                <=> ( v3_pre_topc(X2,X0)
                    & r2_hidden(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <~> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <~> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v3_pre_topc(X2,X0)
                | ~ r2_hidden(X1,X2)
                | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
              & ( ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) )
                | r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v3_pre_topc(X2,X0)
                | ~ r2_hidden(X1,X2)
                | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
              & ( ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) )
                | r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ v3_pre_topc(X2,X0)
            | ~ r2_hidden(X1,X2)
            | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & ( ( v3_pre_topc(X2,X0)
              & r2_hidden(X1,X2) )
            | r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v3_pre_topc(sK4,X0)
          | ~ r2_hidden(X1,sK4)
          | ~ r2_hidden(sK4,u1_struct_0(k9_yellow_6(X0,X1))) )
        & ( ( v3_pre_topc(sK4,X0)
            & r2_hidden(X1,sK4) )
          | r2_hidden(sK4,u1_struct_0(k9_yellow_6(X0,X1))) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v3_pre_topc(X2,X0)
                | ~ r2_hidden(X1,X2)
                | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
              & ( ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) )
                | r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ~ v3_pre_topc(X2,X0)
              | ~ r2_hidden(sK3,X2)
              | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,sK3))) )
            & ( ( v3_pre_topc(X2,X0)
                & r2_hidden(sK3,X2) )
              | r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,sK3))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X1,X2)
                  | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
                & ( ( v3_pre_topc(X2,X0)
                    & r2_hidden(X1,X2) )
                  | r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v3_pre_topc(X2,sK2)
                | ~ r2_hidden(X1,X2)
                | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(sK2,X1))) )
              & ( ( v3_pre_topc(X2,sK2)
                  & r2_hidden(X1,X2) )
                | r2_hidden(X2,u1_struct_0(k9_yellow_6(sK2,X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ( ~ v3_pre_topc(sK4,sK2)
      | ~ r2_hidden(sK3,sK4)
      | ~ r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) )
    & ( ( v3_pre_topc(sK4,sK2)
        & r2_hidden(sK3,sK4) )
      | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f45,f48,f47,f46])).

fof(f75,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k9_yellow_6(X0,X1) = k7_lattice3(g1_orders_2(a_2_0_yellow_6(X0,X1),k1_yellow_1(a_2_0_yellow_6(X0,X1))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f74,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f72,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f73,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f79,plain,
    ( ~ v3_pre_topc(sK4,sK2)
    | ~ r2_hidden(sK3,sK4)
    | ~ r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,
    ( v3_pre_topc(sK4,sK2)
    | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( v3_pre_topc(X3,X0)
          & r2_hidden(X1,X3)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_pre_topc(sK1(X0,X1,X2),X0)
        & r2_hidden(X1,sK1(X0,X1,X2))
        & sK1(X0,X1,X2) = X2
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_pre_topc(sK1(X0,X1,X2),X0)
                & r2_hidden(X1,sK1(X0,X1,X2))
                & sK1(X0,X1,X2) = X2
                & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f42])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK1(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( sK1(X0,X1,X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,
    ( r2_hidden(sK3,sK4)
    | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f49])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK1(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_yellow_6(X1,X2))
      <=> ? [X3] :
            ( v3_pre_topc(X3,X1)
            & r2_hidden(X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_yellow_6(X1,X2))
      <=> ? [X3] :
            ( v3_pre_topc(X3,X1)
            & r2_hidden(X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_yellow_6(X1,X2))
      <=> ? [X3] :
            ( v3_pre_topc(X3,X1)
            & r2_hidden(X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f24])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_yellow_6(X1,X2))
          | ! [X3] :
              ( ~ v3_pre_topc(X3,X1)
              | ~ r2_hidden(X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ? [X3] :
              ( v3_pre_topc(X3,X1)
              & r2_hidden(X2,X3)
              & X0 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_0_yellow_6(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_yellow_6(X1,X2))
          | ! [X3] :
              ( ~ v3_pre_topc(X3,X1)
              | ~ r2_hidden(X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ? [X4] :
              ( v3_pre_topc(X4,X1)
              & r2_hidden(X2,X4)
              & X0 = X4
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_0_yellow_6(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( v3_pre_topc(X4,X1)
          & r2_hidden(X2,X4)
          & X0 = X4
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v3_pre_topc(sK0(X0,X1,X2),X1)
        & r2_hidden(X2,sK0(X0,X1,X2))
        & sK0(X0,X1,X2) = X0
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_yellow_6(X1,X2))
          | ! [X3] :
              ( ~ v3_pre_topc(X3,X1)
              | ~ r2_hidden(X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ( v3_pre_topc(sK0(X0,X1,X2),X1)
            & r2_hidden(X2,sK0(X0,X1,X2))
            & sK0(X0,X1,X2) = X0
            & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_0_yellow_6(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_yellow_6(X1,X2))
      | ~ v3_pre_topc(X3,X1)
      | ~ r2_hidden(X2,X3)
      | X0 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f83,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_0_yellow_6(X1,X2))
      | ~ v3_pre_topc(X3,X1)
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f60])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3,plain,
    ( l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1771,plain,
    ( l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1773,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
    | l1_orders_2(X0) != iProver_top
    | v1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2673,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) = g1_orders_2(X0,k1_yellow_1(X0))
    | v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1771,c_1773])).

cnf(c_4,plain,
    ( v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_323,plain,
    ( ~ l1_orders_2(X0)
    | g1_orders_2(X1,k1_yellow_1(X1)) != X0
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_324,plain,
    ( ~ l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))
    | g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_4483,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2673,c_3,c_324])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1768,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4487,plain,
    ( g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2)
    | u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X1
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4483,c_1768])).

cnf(c_4570,plain,
    ( u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X0
    | m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4487])).

cnf(c_2,plain,
    ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_89,plain,
    ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7044,plain,
    ( u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4570,c_89])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1758,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k7_lattice3(g1_orders_2(a_2_0_yellow_6(X1,X0),k1_yellow_1(a_2_0_yellow_6(X1,X0)))) = k9_yellow_6(X1,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_717,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | k7_lattice3(g1_orders_2(a_2_0_yellow_6(X1,X0),k1_yellow_1(a_2_0_yellow_6(X1,X0)))) = k9_yellow_6(X1,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_26])).

cnf(c_718,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | k7_lattice3(g1_orders_2(a_2_0_yellow_6(sK2,X0),k1_yellow_1(a_2_0_yellow_6(sK2,X0)))) = k9_yellow_6(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_717])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_722,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k7_lattice3(g1_orders_2(a_2_0_yellow_6(sK2,X0),k1_yellow_1(a_2_0_yellow_6(sK2,X0)))) = k9_yellow_6(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_718,c_28,c_27])).

cnf(c_1749,plain,
    ( k7_lattice3(g1_orders_2(a_2_0_yellow_6(sK2,X0),k1_yellow_1(a_2_0_yellow_6(sK2,X0)))) = k9_yellow_6(sK2,X0)
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_722])).

cnf(c_2066,plain,
    ( k7_lattice3(g1_orders_2(a_2_0_yellow_6(sK2,sK3),k1_yellow_1(a_2_0_yellow_6(sK2,sK3)))) = k9_yellow_6(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1758,c_1749])).

cnf(c_12,plain,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(k7_lattice3(X0)) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1767,plain,
    ( u1_struct_0(k7_lattice3(X0)) = u1_struct_0(X0)
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2570,plain,
    ( u1_struct_0(k7_lattice3(g1_orders_2(X0,k1_yellow_1(X0)))) = u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(superposition,[status(thm)],[c_1771,c_1767])).

cnf(c_3297,plain,
    ( u1_struct_0(g1_orders_2(a_2_0_yellow_6(sK2,sK3),k1_yellow_1(a_2_0_yellow_6(sK2,sK3)))) = u1_struct_0(k9_yellow_6(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_2066,c_2570])).

cnf(c_7054,plain,
    ( u1_struct_0(k9_yellow_6(sK2,sK3)) = a_2_0_yellow_6(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_7044,c_3297])).

cnf(c_21,negated_conjecture,
    ( ~ v3_pre_topc(sK4,sK2)
    | ~ r2_hidden(sK3,sK4)
    | ~ r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1762,plain,
    ( v3_pre_topc(sK4,sK2) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top
    | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_7292,plain,
    ( v3_pre_topc(sK4,sK2) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top
    | r2_hidden(sK4,a_2_0_yellow_6(sK2,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7054,c_1762])).

cnf(c_22,negated_conjecture,
    ( v3_pre_topc(sK4,sK2)
    | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1761,plain,
    ( v3_pre_topc(sK4,sK2) = iProver_top
    | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1766,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2545,plain,
    ( v3_pre_topc(sK4,sK2) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1761,c_1766])).

cnf(c_15,plain,
    ( v3_pre_topc(sK1(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_541,plain,
    ( v3_pre_topc(sK1(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_542,plain,
    ( v3_pre_topc(sK1(sK2,X0,X1),sK2)
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_546,plain,
    ( v3_pre_topc(sK1(sK2,X0,X1),sK2)
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_542,c_28,c_27])).

cnf(c_1757,plain,
    ( v3_pre_topc(sK1(sK2,X0,X1),sK2) = iProver_top
    | m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_546])).

cnf(c_2965,plain,
    ( v3_pre_topc(sK1(sK2,sK3,sK4),sK2) = iProver_top
    | v3_pre_topc(sK4,sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_1757])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1275,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1306,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1275])).

cnf(c_2282,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1275])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0,X2) = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_583,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK1(X1,X0,X2) = X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_584,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | sK1(sK2,X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_583])).

cnf(c_588,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | sK1(sK2,X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_584,c_28,c_27])).

cnf(c_1755,plain,
    ( sK1(sK2,X0,X1) = X1
    | m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_588])).

cnf(c_2967,plain,
    ( sK1(sK2,sK3,sK4) = sK4
    | v3_pre_topc(sK4,sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_1755])).

cnf(c_1276,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_2643,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_1276])).

cnf(c_3159,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2643])).

cnf(c_3942,plain,
    ( sK1(sK2,sK3,sK4) != sK4
    | sK4 = sK1(sK2,sK3,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3159])).

cnf(c_1288,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2101,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(sK1(sK2,sK3,X2),sK2)
    | X0 != sK1(sK2,sK3,X2)
    | X1 != sK2 ),
    inference(instantiation,[status(thm)],[c_1288])).

cnf(c_3827,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(sK1(sK2,sK3,sK4),sK2)
    | X0 != sK1(sK2,sK3,sK4)
    | X1 != sK2 ),
    inference(instantiation,[status(thm)],[c_2101])).

cnf(c_4801,plain,
    ( ~ v3_pre_topc(sK1(sK2,sK3,sK4),sK2)
    | v3_pre_topc(sK4,X0)
    | X0 != sK2
    | sK4 != sK1(sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_3827])).

cnf(c_4802,plain,
    ( X0 != sK2
    | sK4 != sK1(sK2,sK3,sK4)
    | v3_pre_topc(sK1(sK2,sK3,sK4),sK2) != iProver_top
    | v3_pre_topc(sK4,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4801])).

cnf(c_4804,plain,
    ( sK2 != sK2
    | sK4 != sK1(sK2,sK3,sK4)
    | v3_pre_topc(sK1(sK2,sK3,sK4),sK2) != iProver_top
    | v3_pre_topc(sK4,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4802])).

cnf(c_4831,plain,
    ( v3_pre_topc(sK4,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2965,c_32,c_1306,c_2282,c_2967,c_3942,c_4804])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK3,sK4)
    | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1760,plain,
    ( r2_hidden(sK3,sK4) = iProver_top
    | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2546,plain,
    ( r2_hidden(sK3,sK4) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1760,c_1766])).

cnf(c_2995,plain,
    ( sK1(sK2,sK3,sK4) = sK4
    | r2_hidden(sK3,sK4) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_1755])).

cnf(c_2300,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1275])).

cnf(c_16,plain,
    ( r2_hidden(X0,sK1(X1,X0,X2))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_604,plain,
    ( r2_hidden(X0,sK1(X1,X0,X2))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_605,plain,
    ( r2_hidden(X0,sK1(sK2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_604])).

cnf(c_609,plain,
    ( r2_hidden(X0,sK1(sK2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_605,c_28,c_27])).

cnf(c_1754,plain,
    ( r2_hidden(X0,sK1(sK2,X0,X1)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK2,X0))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_609])).

cnf(c_2994,plain,
    ( r2_hidden(sK3,sK1(sK2,sK3,sK4)) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_1754])).

cnf(c_1287,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2145,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK3,sK1(sK2,sK3,X2))
    | X1 != sK1(sK2,sK3,X2)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1287])).

cnf(c_2589,plain,
    ( r2_hidden(sK3,X0)
    | ~ r2_hidden(sK3,sK1(sK2,sK3,X1))
    | X0 != sK1(sK2,sK3,X1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2145])).

cnf(c_3843,plain,
    ( r2_hidden(sK3,X0)
    | ~ r2_hidden(sK3,sK1(sK2,sK3,sK4))
    | X0 != sK1(sK2,sK3,sK4)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2589])).

cnf(c_4682,plain,
    ( ~ r2_hidden(sK3,sK1(sK2,sK3,sK4))
    | r2_hidden(sK3,sK4)
    | sK3 != sK3
    | sK4 != sK1(sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_3843])).

cnf(c_4683,plain,
    ( sK3 != sK3
    | sK4 != sK1(sK2,sK3,sK4)
    | r2_hidden(sK3,sK1(sK2,sK3,sK4)) != iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4682])).

cnf(c_4772,plain,
    ( r2_hidden(sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2995,c_32,c_2282,c_2300,c_2994,c_3942,c_4683])).

cnf(c_5,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,a_2_0_yellow_6(X1,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_688,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,a_2_0_yellow_6(X1,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_26])).

cnf(c_689,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,a_2_0_yellow_6(sK2,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_688])).

cnf(c_693,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,a_2_0_yellow_6(sK2,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_689,c_28,c_27])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_709,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,a_2_0_yellow_6(sK2,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_693,c_19])).

cnf(c_2227,plain,
    ( ~ v3_pre_topc(sK4,sK2)
    | ~ r2_hidden(X0,sK4)
    | r2_hidden(sK4,a_2_0_yellow_6(sK2,X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_709])).

cnf(c_2517,plain,
    ( ~ v3_pre_topc(sK4,sK2)
    | ~ r2_hidden(sK3,sK4)
    | r2_hidden(sK4,a_2_0_yellow_6(sK2,sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_2227])).

cnf(c_2518,plain,
    ( v3_pre_topc(sK4,sK2) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top
    | r2_hidden(sK4,a_2_0_yellow_6(sK2,sK3)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2517])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_33,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7292,c_4831,c_4772,c_2518,c_33])).


%------------------------------------------------------------------------------
