%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1617+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:59 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1073)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = k2_yellow_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = k2_yellow_1(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0] : k1_yellow_1(X0) = k1_wellord2(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k1_yellow_1(X0) = k1_wellord2(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0] : g1_orders_2(X0,k1_wellord2(X0)) = k2_yellow_1(X0) ),
    inference(definition_unfolding,[],[f49,f60])).

fof(f70,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_wellord2(X0))) ),
    inference(definition_unfolding,[],[f57,f68])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f44,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    ! [X0] : v1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f71,plain,(
    ! [X0] : v1_orders_2(g1_orders_2(X0,k1_wellord2(X0))) ),
    inference(definition_unfolding,[],[f56,f68])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k1_yellow_1(X0),X0)
      & v8_relat_2(k1_yellow_1(X0))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v8_relat_2(k1_yellow_1(X0))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f16,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f17,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k1_wellord2(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f55,f60])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v1_tops_2(X1,X0)
            <=> m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f14,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v1_tops_2(X1,X0)
            <=> m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_2(X1,X0)
          <~> m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
            | ~ v1_tops_2(X1,X0) )
          & ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
            | ~ v1_tops_2(X1,X0) )
          & ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
            | ~ v1_tops_2(X1,X0) )
          & ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
          | ~ v1_tops_2(sK3,X0) )
        & ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
          | v1_tops_2(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
              | ~ v1_tops_2(X1,X0) )
            & ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
              | v1_tops_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK2)))))
            | ~ v1_tops_2(X1,sK2) )
          & ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK2)))))
            | v1_tops_2(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK2)))))
      | ~ v1_tops_2(sK3,sK2) )
    & ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK2)))))
      | v1_tops_2(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f40,f42,f41])).

fof(f66,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK2)))))
    | v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_pre_topc(sK2),k1_wellord2(u1_pre_topc(sK2))))))
    | v1_tops_2(sK3,sK2) ),
    inference(definition_unfolding,[],[f66,f68])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK0(X0,X1),X0)
        & r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK0(X0,X1),X0)
                & r2_hidden(sK0(X0,X1),X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | r2_hidden(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v3_pre_topc(sK0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f67,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK2)))))
    | ~ v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_pre_topc(sK2),k1_wellord2(u1_pre_topc(sK2))))))
    | ~ v1_tops_2(sK3,sK2) ),
    inference(definition_unfolding,[],[f67,f68])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_855,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_11,plain,
    ( l1_orders_2(g1_orders_2(X0,k1_wellord2(X0))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_850,plain,
    ( l1_orders_2(g1_orders_2(X0,k1_wellord2(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_861,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
    | l1_orders_2(X0) != iProver_top
    | v1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2123,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_wellord2(X0))),u1_orders_2(g1_orders_2(X0,k1_wellord2(X0)))) = g1_orders_2(X0,k1_wellord2(X0))
    | v1_orders_2(g1_orders_2(X0,k1_wellord2(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_850,c_861])).

cnf(c_12,plain,
    ( v1_orders_2(g1_orders_2(X0,k1_wellord2(X0))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1063,plain,
    ( ~ l1_orders_2(g1_orders_2(X0,k1_wellord2(X0)))
    | ~ v1_orders_2(g1_orders_2(X0,k1_wellord2(X0)))
    | g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_wellord2(X0))),u1_orders_2(g1_orders_2(X0,k1_wellord2(X0)))) = g1_orders_2(X0,k1_wellord2(X0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_6625,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_wellord2(X0))),u1_orders_2(g1_orders_2(X0,k1_wellord2(X0)))) = g1_orders_2(X0,k1_wellord2(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2123,c_12,c_11,c_1063])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_847,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6629,plain,
    ( g1_orders_2(X0,k1_wellord2(X0)) != g1_orders_2(X1,X2)
    | u1_struct_0(g1_orders_2(X0,k1_wellord2(X0))) = X1
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6625,c_847])).

cnf(c_7573,plain,
    ( u1_struct_0(g1_orders_2(X0,k1_wellord2(X0))) = X0
    | m1_subset_1(k1_wellord2(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_6629])).

cnf(c_10,plain,
    ( m1_subset_1(k1_wellord2(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_45,plain,
    ( m1_subset_1(k1_wellord2(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7753,plain,
    ( u1_struct_0(g1_orders_2(X0,k1_wellord2(X0))) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7573,c_45])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_pre_topc(sK2),k1_wellord2(u1_pre_topc(sK2))))))
    | v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_842,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_pre_topc(sK2),k1_wellord2(u1_pre_topc(sK2)))))) = iProver_top
    | v1_tops_2(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7764,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_pre_topc(sK2))) = iProver_top
    | v1_tops_2(sK3,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7753,c_842])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1358,plain,
    ( r1_tarski(X0,X0) ),
    inference(resolution,[status(thm)],[c_5,c_6])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | v1_tops_2(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3573,plain,
    ( r2_hidden(sK0(sK2,sK3),sK3)
    | v1_tops_2(sK3,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_2,c_20])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_841,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_859,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | v1_tops_2(X1,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3145,plain,
    ( r2_hidden(sK0(sK2,sK3),sK3) = iProver_top
    | v1_tops_2(sK3,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_841,c_859])).

cnf(c_3163,plain,
    ( r2_hidden(sK0(sK2,sK3),sK3)
    | v1_tops_2(sK3,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3145])).

cnf(c_3705,plain,
    ( v1_tops_2(sK3,sK2)
    | r2_hidden(sK0(sK2,sK3),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3573,c_21,c_20,c_1073])).

cnf(c_3706,plain,
    ( r2_hidden(sK0(sK2,sK3),sK3)
    | v1_tops_2(sK3,sK2) ),
    inference(renaming,[status(thm)],[c_3705])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_3722,plain,
    ( ~ r1_tarski(sK3,X0)
    | r2_hidden(sK0(sK2,sK3),X0)
    | v1_tops_2(sK3,sK2) ),
    inference(resolution,[status(thm)],[c_3706,c_7])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1669,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | m1_subset_1(X2,X1) ),
    inference(resolution,[status(thm)],[c_17,c_15])).

cnf(c_3907,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(sK3,X0)
    | m1_subset_1(sK0(sK2,sK3),X1)
    | v1_tops_2(sK3,sK2) ),
    inference(resolution,[status(thm)],[c_3722,c_1669])).

cnf(c_16,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1106,plain,
    ( r1_tarski(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[status(thm)],[c_16,c_20])).

cnf(c_4036,plain,
    ( ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK2)),X0)
    | m1_subset_1(sK0(sK2,sK3),X0)
    | v1_tops_2(sK3,sK2) ),
    inference(resolution,[status(thm)],[c_3907,c_1106])).

cnf(c_5752,plain,
    ( m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_tops_2(sK3,sK2) ),
    inference(resolution,[status(thm)],[c_1358,c_4036])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_6227,plain,
    ( ~ r2_hidden(sK0(sK2,sK3),u1_pre_topc(sK2))
    | v3_pre_topc(sK0(sK2,sK3),sK2)
    | v1_tops_2(sK3,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_5752,c_8])).

cnf(c_1673,plain,
    ( ~ r2_hidden(X0,sK3)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[status(thm)],[c_17,c_20])).

cnf(c_2255,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(sK2))
    | ~ r2_hidden(X0,sK3)
    | v3_pre_topc(X0,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_8,c_1673])).

cnf(c_2270,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,u1_pre_topc(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2255,c_21])).

cnf(c_2271,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(sK2))
    | ~ r2_hidden(X0,sK3)
    | v3_pre_topc(X0,sK2) ),
    inference(renaming,[status(thm)],[c_2270])).

cnf(c_3920,plain,
    ( ~ r1_tarski(sK3,u1_pre_topc(sK2))
    | ~ r2_hidden(sK0(sK2,sK3),sK3)
    | v3_pre_topc(sK0(sK2,sK3),sK2)
    | v1_tops_2(sK3,sK2) ),
    inference(resolution,[status(thm)],[c_3722,c_2271])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v3_pre_topc(sK0(X1,X0),X1)
    | v1_tops_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_860,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | v3_pre_topc(sK0(X1,X0),X1) != iProver_top
    | v1_tops_2(X0,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3170,plain,
    ( v3_pre_topc(sK0(sK2,sK3),sK2) != iProver_top
    | v1_tops_2(sK3,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_841,c_860])).

cnf(c_3188,plain,
    ( ~ v3_pre_topc(sK0(sK2,sK3),sK2)
    | v1_tops_2(sK3,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3170])).

cnf(c_5144,plain,
    ( ~ r1_tarski(sK3,u1_pre_topc(sK2))
    | v1_tops_2(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3920,c_21,c_3163,c_3188])).

cnf(c_845,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1311,plain,
    ( r1_tarski(sK3,u1_struct_0(g1_orders_2(u1_pre_topc(sK2),k1_wellord2(u1_pre_topc(sK2))))) = iProver_top
    | v1_tops_2(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_842,c_845])).

cnf(c_7762,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2)) = iProver_top
    | v1_tops_2(sK3,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7753,c_1311])).

cnf(c_7841,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2))
    | v1_tops_2(sK3,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7762])).

cnf(c_8037,plain,
    ( v1_tops_2(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6227,c_5144,c_7841])).

cnf(c_8039,plain,
    ( v1_tops_2(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8037])).

cnf(c_8122,plain,
    ( v1_tops_2(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7764,c_8039])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_857,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | v3_pre_topc(X0,X2) = iProver_top
    | v1_tops_2(X1,X2) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_844,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_972,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) != iProver_top
    | v3_pre_topc(X0,X2) = iProver_top
    | v1_tops_2(X1,X2) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_857,c_844])).

cnf(c_4173,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | v3_pre_topc(X0,sK2) = iProver_top
    | v1_tops_2(sK3,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_841,c_972])).

cnf(c_22,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4344,plain,
    ( v1_tops_2(sK3,sK2) != iProver_top
    | v3_pre_topc(X0,sK2) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4173,c_22])).

cnf(c_4345,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | v3_pre_topc(X0,sK2) = iProver_top
    | v1_tops_2(sK3,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4344])).

cnf(c_8127,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | v3_pre_topc(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_8122,c_4345])).

cnf(c_8440,plain,
    ( r1_tarski(sK3,X0) = iProver_top
    | v3_pre_topc(sK1(sK3,X0),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_855,c_8127])).

cnf(c_1186,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_841,c_844])).

cnf(c_9,plain,
    ( r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_852,plain,
    ( r2_hidden(X0,u1_pre_topc(X1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v3_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2200,plain,
    ( r2_hidden(X0,u1_pre_topc(sK2)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | v3_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1186,c_852])).

cnf(c_2380,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2200,c_22])).

cnf(c_2381,plain,
    ( r2_hidden(X0,u1_pre_topc(sK2)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | v3_pre_topc(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2380])).

cnf(c_856,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2390,plain,
    ( r1_tarski(X0,u1_pre_topc(sK2)) = iProver_top
    | r2_hidden(sK1(X0,u1_pre_topc(sK2)),sK3) != iProver_top
    | v3_pre_topc(sK1(X0,u1_pre_topc(sK2)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2381,c_856])).

cnf(c_4544,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2)) = iProver_top
    | v3_pre_topc(sK1(sK3,u1_pre_topc(sK2)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_855,c_2390])).

cnf(c_8462,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8440,c_4544])).

cnf(c_846,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_18,negated_conjecture,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_pre_topc(sK2),k1_wellord2(u1_pre_topc(sK2))))))
    | ~ v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_843,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_pre_topc(sK2),k1_wellord2(u1_pre_topc(sK2)))))) != iProver_top
    | v1_tops_2(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1329,plain,
    ( r1_tarski(sK3,u1_struct_0(g1_orders_2(u1_pre_topc(sK2),k1_wellord2(u1_pre_topc(sK2))))) != iProver_top
    | v1_tops_2(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_846,c_843])).

cnf(c_7763,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2)) != iProver_top
    | v1_tops_2(sK3,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7753,c_1329])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8462,c_8039,c_7763])).


%------------------------------------------------------------------------------
