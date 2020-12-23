%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1941+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  125 (2246 expanded)
%              Number of clauses        :   63 ( 480 expanded)
%              Number of leaves         :   14 ( 602 expanded)
%              Depth                    :   24
%              Number of atoms          :  503 (13494 expanded)
%              Number of equality atoms :  147 (1286 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ v3_pre_topc(X2,X0)
            | ~ r2_hidden(X1,X2)
            | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & ( ( v3_pre_topc(X2,X0)
              & r2_hidden(X1,X2) )
            | r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v3_pre_topc(sK3,X0)
          | ~ r2_hidden(X1,sK3)
          | ~ r2_hidden(sK3,u1_struct_0(k9_yellow_6(X0,X1))) )
        & ( ( v3_pre_topc(sK3,X0)
            & r2_hidden(X1,sK3) )
          | r2_hidden(sK3,u1_struct_0(k9_yellow_6(X0,X1))) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
              | ~ r2_hidden(sK2,X2)
              | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,sK2))) )
            & ( ( v3_pre_topc(X2,X0)
                & r2_hidden(sK2,X2) )
              | r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,sK2))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
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
              ( ( ~ v3_pre_topc(X2,sK1)
                | ~ r2_hidden(X1,X2)
                | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(sK1,X1))) )
              & ( ( v3_pre_topc(X2,sK1)
                  & r2_hidden(X1,X2) )
                | r2_hidden(X2,u1_struct_0(k9_yellow_6(sK1,X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( ~ v3_pre_topc(sK3,sK1)
      | ~ r2_hidden(sK2,sK3)
      | ~ r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) )
    & ( ( v3_pre_topc(sK3,sK1)
        & r2_hidden(sK2,sK3) )
      | r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f37,f36,f35])).

fof(f58,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = k2_yellow_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = k2_yellow_1(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0] : k1_yellow_1(X0) = k1_wellord2(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k1_yellow_1(X0) = k1_wellord2(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X0] : g1_orders_2(X0,k1_wellord2(X0)) = k2_yellow_1(X0) ),
    inference(definition_unfolding,[],[f41,f52])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k9_yellow_6(X0,X1) = k7_lattice3(g1_orders_2(a_2_0_yellow_6(X0,X1),k1_wellord2(a_2_0_yellow_6(X0,X1))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f40,f63])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f56,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f57,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_wellord2(X0))) ),
    inference(definition_unfolding,[],[f44,f63])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f39,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0] : v1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f67,plain,(
    ! [X0] : v1_orders_2(g1_orders_2(X0,k1_wellord2(X0))) ),
    inference(definition_unfolding,[],[f43,f63])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k1_yellow_1(X0),X0)
      & v8_relat_2(k1_yellow_1(X0))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v8_relat_2(k1_yellow_1(X0))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f14,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f16,plain,(
    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k1_wellord2(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f42,f52])).

fof(f61,plain,
    ( v3_pre_topc(sK3,sK1)
    | r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,
    ( r2_hidden(sK2,sK3)
    | r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | ~ r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f49,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_0_yellow_6(X1,X2))
      | ~ v3_pre_topc(X3,X1)
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f49])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( sK0(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_yellow_6(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,sK0(X0,X1,X2))
      | ~ r2_hidden(X0,a_2_0_yellow_6(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(X0,a_2_0_yellow_6(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_624,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k7_lattice3(g1_orders_2(a_2_0_yellow_6(X1,X0),k1_wellord2(a_2_0_yellow_6(X1,X0)))) = k9_yellow_6(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_641,plain,
    ( k7_lattice3(g1_orders_2(a_2_0_yellow_6(X0,X1),k1_wellord2(a_2_0_yellow_6(X0,X1)))) = k9_yellow_6(X0,X1)
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1680,plain,
    ( k7_lattice3(g1_orders_2(a_2_0_yellow_6(sK1,sK2),k1_wellord2(a_2_0_yellow_6(sK1,sK2)))) = k9_yellow_6(sK1,sK2)
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_624,c_641])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_911,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | k7_lattice3(g1_orders_2(a_2_0_yellow_6(sK1,sK2),k1_wellord2(a_2_0_yellow_6(sK1,sK2)))) = k9_yellow_6(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1906,plain,
    ( k7_lattice3(g1_orders_2(a_2_0_yellow_6(sK1,sK2),k1_wellord2(a_2_0_yellow_6(sK1,sK2)))) = k9_yellow_6(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1680,c_21,c_20,c_19,c_18,c_911])).

cnf(c_3,plain,
    ( l1_orders_2(g1_orders_2(X0,k1_wellord2(X0))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_639,plain,
    ( l1_orders_2(g1_orders_2(X0,k1_wellord2(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_12,plain,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(k7_lattice3(X0)) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_630,plain,
    ( u1_struct_0(k7_lattice3(X0)) = u1_struct_0(X0)
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1303,plain,
    ( u1_struct_0(k7_lattice3(g1_orders_2(X0,k1_wellord2(X0)))) = u1_struct_0(g1_orders_2(X0,k1_wellord2(X0))) ),
    inference(superposition,[status(thm)],[c_639,c_630])).

cnf(c_1909,plain,
    ( u1_struct_0(g1_orders_2(a_2_0_yellow_6(sK1,sK2),k1_wellord2(a_2_0_yellow_6(sK1,sK2)))) = u1_struct_0(k9_yellow_6(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1906,c_1303])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_642,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
    | l1_orders_2(X0) != iProver_top
    | v1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1514,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_wellord2(X0))),u1_orders_2(g1_orders_2(X0,k1_wellord2(X0)))) = g1_orders_2(X0,k1_wellord2(X0))
    | v1_orders_2(g1_orders_2(X0,k1_wellord2(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_639,c_642])).

cnf(c_4,plain,
    ( v1_orders_2(g1_orders_2(X0,k1_wellord2(X0))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_947,plain,
    ( ~ l1_orders_2(g1_orders_2(X0,k1_wellord2(X0)))
    | ~ v1_orders_2(g1_orders_2(X0,k1_wellord2(X0)))
    | g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_wellord2(X0))),u1_orders_2(g1_orders_2(X0,k1_wellord2(X0)))) = g1_orders_2(X0,k1_wellord2(X0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2171,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_wellord2(X0))),u1_orders_2(g1_orders_2(X0,k1_wellord2(X0)))) = g1_orders_2(X0,k1_wellord2(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1514,c_4,c_3,c_947])).

cnf(c_2175,plain,
    ( g1_orders_2(u1_struct_0(k9_yellow_6(sK1,sK2)),u1_orders_2(g1_orders_2(a_2_0_yellow_6(sK1,sK2),k1_wellord2(a_2_0_yellow_6(sK1,sK2))))) = g1_orders_2(a_2_0_yellow_6(sK1,sK2),k1_wellord2(a_2_0_yellow_6(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_1909,c_2171])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_631,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2338,plain,
    ( g1_orders_2(a_2_0_yellow_6(sK1,sK2),k1_wellord2(a_2_0_yellow_6(sK1,sK2))) != g1_orders_2(X0,X1)
    | u1_struct_0(k9_yellow_6(sK1,sK2)) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2175,c_631])).

cnf(c_2384,plain,
    ( u1_struct_0(k9_yellow_6(sK1,sK2)) = a_2_0_yellow_6(sK1,sK2)
    | m1_subset_1(k1_wellord2(a_2_0_yellow_6(sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(a_2_0_yellow_6(sK1,sK2),a_2_0_yellow_6(sK1,sK2)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2338])).

cnf(c_2,plain,
    ( m1_subset_1(k1_wellord2(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_640,plain,
    ( m1_subset_1(k1_wellord2(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3559,plain,
    ( u1_struct_0(k9_yellow_6(sK1,sK2)) = a_2_0_yellow_6(sK1,sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2384,c_640])).

cnf(c_15,negated_conjecture,
    ( v3_pre_topc(sK3,sK1)
    | r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_627,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3570,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | r2_hidden(sK3,a_2_0_yellow_6(sK1,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3559,c_627])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK2,sK3)
    | r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_626,plain,
    ( r2_hidden(sK2,sK3) = iProver_top
    | r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3571,plain,
    ( r2_hidden(sK2,sK3) = iProver_top
    | r2_hidden(sK3,a_2_0_yellow_6(sK1,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3559,c_626])).

cnf(c_14,negated_conjecture,
    ( ~ v3_pre_topc(sK3,sK1)
    | ~ r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_628,plain,
    ( v3_pre_topc(sK3,sK1) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top
    | r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3572,plain,
    ( v3_pre_topc(sK3,sK1) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top
    | r2_hidden(sK3,a_2_0_yellow_6(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3559,c_628])).

cnf(c_22,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_23,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_24,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_25,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,a_2_0_yellow_6(X1,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3205,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | ~ r2_hidden(X0,sK3)
    | r2_hidden(sK3,a_2_0_yellow_6(sK1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3545,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | ~ r2_hidden(sK2,sK3)
    | r2_hidden(sK3,a_2_0_yellow_6(sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3205])).

cnf(c_3546,plain,
    ( v3_pre_topc(sK3,sK1) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top
    | r2_hidden(sK3,a_2_0_yellow_6(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3545])).

cnf(c_3708,plain,
    ( r2_hidden(sK2,sK3) != iProver_top
    | v3_pre_topc(sK3,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3572,c_22,c_23,c_24,c_25,c_26,c_3546])).

cnf(c_3709,plain,
    ( v3_pre_topc(sK3,sK1) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3708])).

cnf(c_3950,plain,
    ( r2_hidden(sK3,a_2_0_yellow_6(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3570,c_3571,c_3709])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,a_2_0_yellow_6(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_634,plain,
    ( sK0(X0,X1,X2) = X0
    | r2_hidden(X0,a_2_0_yellow_6(X1,X2)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3955,plain,
    ( sK0(sK3,sK1,sK2) = sK3
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3950,c_634])).

cnf(c_4022,plain,
    ( sK0(sK3,sK1,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3955,c_22,c_23,c_24,c_25])).

cnf(c_7,plain,
    ( r2_hidden(X0,sK0(X1,X2,X0))
    | ~ r2_hidden(X1,a_2_0_yellow_6(X2,X0))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_635,plain,
    ( r2_hidden(X0,sK0(X1,X2,X0)) = iProver_top
    | r2_hidden(X1,a_2_0_yellow_6(X2,X0)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(X2)) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4027,plain,
    ( r2_hidden(sK2,sK3) = iProver_top
    | r2_hidden(sK3,a_2_0_yellow_6(sK1,sK2)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4022,c_635])).

cnf(c_6,plain,
    ( v3_pre_topc(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(X0,a_2_0_yellow_6(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_636,plain,
    ( v3_pre_topc(sK0(X0,X1,X2),X1) = iProver_top
    | r2_hidden(X0,a_2_0_yellow_6(X1,X2)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4026,plain,
    ( v3_pre_topc(sK3,sK1) = iProver_top
    | r2_hidden(sK3,a_2_0_yellow_6(sK1,sK2)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4022,c_636])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4027,c_4026,c_3950,c_3572,c_25,c_24,c_23,c_22])).


%------------------------------------------------------------------------------
