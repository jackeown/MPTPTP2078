%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1617+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:10 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 445 expanded)
%              Number of leaves         :   18 ( 120 expanded)
%              Depth                    :   22
%              Number of atoms          :  367 (1799 expanded)
%              Number of equality atoms :   23 ( 105 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f338,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f303,f337,f251])).

fof(f251,plain,
    ( ~ r1_tarski(sK3,u1_pre_topc(sK2))
    | ~ v1_tops_2(sK3,sK2) ),
    inference(backward_demodulation,[],[f103,f241])).

fof(f241,plain,(
    ! [X2] : u1_struct_0(g1_orders_2(X2,k1_wellord2(X2))) = X2 ),
    inference(subsumption_resolution,[],[f240,f80])).

fof(f80,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_wellord2(X0))) ),
    inference(definition_unfolding,[],[f57,f76])).

fof(f76,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_wellord2(X0)) ),
    inference(definition_unfolding,[],[f54,f53])).

fof(f53,plain,(
    ! [X0] : k1_yellow_1(X0) = k1_wellord2(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_yellow_1(X0) = k1_wellord2(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_yellow_1)).

fof(f54,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

fof(f57,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f240,plain,(
    ! [X2] :
      ( u1_struct_0(g1_orders_2(X2,k1_wellord2(X2))) = X2
      | ~ l1_orders_2(g1_orders_2(X2,k1_wellord2(X2))) ) ),
    inference(subsumption_resolution,[],[f237,f81])).

fof(f81,plain,(
    ! [X0] : v1_orders_2(g1_orders_2(X0,k1_wellord2(X0))) ),
    inference(definition_unfolding,[],[f56,f76])).

fof(f56,plain,(
    ! [X0] : v1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f237,plain,(
    ! [X2] :
      ( u1_struct_0(g1_orders_2(X2,k1_wellord2(X2))) = X2
      | ~ v1_orders_2(g1_orders_2(X2,k1_wellord2(X2)))
      | ~ l1_orders_2(g1_orders_2(X2,k1_wellord2(X2))) ) ),
    inference(resolution,[],[f183,f79])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k1_wellord2(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f55,f53])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v8_relat_2(k1_yellow_1(X0))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k1_yellow_1(X0),X0)
      & v8_relat_2(k1_yellow_1(X0))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_1)).

fof(f183,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | u1_struct_0(g1_orders_2(X0,X1)) = X0
      | ~ v1_orders_2(g1_orders_2(X0,X1))
      | ~ l1_orders_2(g1_orders_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(X1,X2) != X0
      | u1_struct_0(X0) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(superposition,[],[f68,f58])).

fof(f58,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f103,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(g1_orders_2(u1_pre_topc(sK2),k1_wellord2(u1_pre_topc(sK2)))))
    | ~ v1_tops_2(sK3,sK2) ),
    inference(resolution,[],[f77,f74])).

% (5642)Termination reason: Refutation not found, incomplete strategy

% (5642)Memory used [KB]: 10746
% (5642)Time elapsed: 0.069 s
% (5642)------------------------------
% (5642)------------------------------
fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f77,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_pre_topc(sK2),k1_wellord2(u1_pre_topc(sK2))))))
    | ~ v1_tops_2(sK3,sK2) ),
    inference(definition_unfolding,[],[f52,f76])).

fof(f52,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK2)))))
    | ~ v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f36])).

% (5639)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f36,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK2)))))
      | ~ v1_tops_2(sK3,sK2) )
    & ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK2)))))
      | v1_tops_2(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f33,f35,f34])).

fof(f34,plain,
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

fof(f35,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK2)))))
          | ~ v1_tops_2(X1,sK2) )
        & ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK2)))))
          | v1_tops_2(X1,sK2) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK2)))))
        | ~ v1_tops_2(sK3,sK2) )
      & ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK2)))))
        | v1_tops_2(sK3,sK2) )
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
            | ~ v1_tops_2(X1,X0) )
          & ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
            | ~ v1_tops_2(X1,X0) )
          & ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_2(X1,X0)
          <~> m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v1_tops_2(X1,X0)
            <=> m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v1_tops_2(X1,X0)
            <=> m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow_1)).

fof(f337,plain,(
    r1_tarski(sK3,u1_pre_topc(sK2)) ),
    inference(duplicate_literal_removal,[],[f336])).

fof(f336,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2))
    | r1_tarski(sK3,u1_pre_topc(sK2)) ),
    inference(resolution,[],[f335,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f335,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK5(X1,u1_pre_topc(sK2)),sK3)
      | r1_tarski(X1,u1_pre_topc(sK2)) ) ),
    inference(subsumption_resolution,[],[f185,f305])).

fof(f305,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | v3_pre_topc(X0,sK2) ) ),
    inference(duplicate_literal_removal,[],[f304])).

fof(f304,plain,(
    ! [X0] :
      ( v3_pre_topc(X0,sK2)
      | ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f300,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK2,X1)
      | v3_pre_topc(X0,sK2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f63,f94])).

fof(f94,plain,(
    ! [X5] :
      ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(X5,sK3) ) ),
    inference(resolution,[],[f75,f50])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X3,X1)
      | v3_pre_topc(X3,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ v3_pre_topc(sK4(X0,X1),X0)
          & r2_hidden(sK4(X0,X1),X1)
          & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v3_pre_topc(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f41,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK4(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ~ v3_pre_topc(X2,X0)
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v3_pre_topc(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ~ v3_pre_topc(X2,X0)
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( v3_pre_topc(X2,X0)
            | ~ r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( v3_pre_topc(X2,X0)
          | ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f300,plain,(
    sP0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f299,f102])).

fof(f102,plain,
    ( ~ v1_tops_2(sK3,sK2)
    | sP0(sK2,sK3) ),
    inference(resolution,[],[f100,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v1_tops_2(X0,X1)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v1_tops_2(X0,X1)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v1_tops_2(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ( ( v1_tops_2(X1,X0)
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v1_tops_2(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ( v1_tops_2(X1,X0)
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f100,plain,(
    sP1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f99,f49])).

fof(f49,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f99,plain,
    ( sP1(sK3,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f67,f50])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | sP1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f24,f30,f29])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).

fof(f299,plain,
    ( v1_tops_2(sK3,sK2)
    | sP0(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f298])).

fof(f298,plain,
    ( v1_tops_2(sK3,sK2)
    | sP0(sK2,sK3)
    | sP0(sK2,sK3) ),
    inference(resolution,[],[f293,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f293,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4(sK2,X1),sK3)
      | v1_tops_2(sK3,sK2)
      | sP0(sK2,X1) ) ),
    inference(subsumption_resolution,[],[f286,f49])).

fof(f286,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4(sK2,X1),sK3)
      | v1_tops_2(sK3,sK2)
      | ~ l1_pre_topc(sK2)
      | sP0(sK2,X1) ) ),
    inference(resolution,[],[f248,f117])).

fof(f117,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(sK4(X3,X4),u1_pre_topc(X3))
      | ~ l1_pre_topc(X3)
      | sP0(X3,X4) ) ),
    inference(subsumption_resolution,[],[f115,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(sK4(X0,X1),X0)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f115,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(sK4(X3,X4),u1_pre_topc(X3))
      | v3_pre_topc(sK4(X3,X4),X3)
      | ~ l1_pre_topc(X3)
      | sP0(X3,X4) ) ),
    inference(resolution,[],[f60,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f248,plain,(
    ! [X1] :
      ( r2_hidden(X1,u1_pre_topc(sK2))
      | ~ r2_hidden(X1,sK3)
      | v1_tops_2(sK3,sK2) ) ),
    inference(backward_demodulation,[],[f156,f241])).

fof(f156,plain,(
    ! [X1] :
      ( r2_hidden(X1,u1_struct_0(g1_orders_2(u1_pre_topc(sK2),k1_wellord2(u1_pre_topc(sK2)))))
      | ~ r2_hidden(X1,sK3)
      | v1_tops_2(sK3,sK2) ) ),
    inference(resolution,[],[f106,f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f106,plain,
    ( r1_tarski(sK3,u1_struct_0(g1_orders_2(u1_pre_topc(sK2),k1_wellord2(u1_pre_topc(sK2)))))
    | v1_tops_2(sK3,sK2) ),
    inference(resolution,[],[f78,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f78,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_pre_topc(sK2),k1_wellord2(u1_pre_topc(sK2))))))
    | v1_tops_2(sK3,sK2) ),
    inference(definition_unfolding,[],[f51,f76])).

fof(f51,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK2)))))
    | v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f185,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(sK5(X1,u1_pre_topc(sK2)),sK2)
      | ~ r2_hidden(sK5(X1,u1_pre_topc(sK2)),sK3)
      | r1_tarski(X1,u1_pre_topc(sK2)) ) ),
    inference(resolution,[],[f111,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f111,plain,(
    ! [X0] :
      ( r2_hidden(X0,u1_pre_topc(sK2))
      | ~ v3_pre_topc(X0,sK2)
      | ~ r2_hidden(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f107,f49])).

fof(f107,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK2)
      | r2_hidden(X0,u1_pre_topc(sK2))
      | ~ l1_pre_topc(sK2)
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f59,f94])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f303,plain,(
    v1_tops_2(sK3,sK2) ),
    inference(resolution,[],[f300,f101])).

fof(f101,plain,
    ( ~ sP0(sK2,sK3)
    | v1_tops_2(sK3,sK2) ),
    inference(resolution,[],[f100,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v1_tops_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

%------------------------------------------------------------------------------
