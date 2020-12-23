%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_1__t25_yellow_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:53 EDT 2019

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 338 expanded)
%              Number of leaves         :   22 (  97 expanded)
%              Depth                    :   18
%              Number of atoms          :  411 (1357 expanded)
%              Number of equality atoms :   23 ( 100 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5292,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f155,f156,f771,f777,f5102,f5289])).

fof(f5289,plain,
    ( ~ spl8_0
    | spl8_3 ),
    inference(avatar_contradiction_clause,[],[f5288])).

fof(f5288,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f5281,f5107])).

fof(f5107,plain,
    ( ~ r1_tarski(sK1,u1_pre_topc(sK0))
    | ~ spl8_3 ),
    inference(resolution,[],[f5104,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_1__t25_yellow_1.p',t3_subset)).

fof(f5104,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_pre_topc(sK0)))
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f154,f3096])).

fof(f3096,plain,(
    ! [X0] : u1_struct_0(g1_orders_2(X0,k1_wellord2(X0))) = X0 ),
    inference(subsumption_resolution,[],[f3095,f136])).

fof(f136,plain,(
    ! [X0] : m1_subset_1(k1_wellord2(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f98,f92])).

fof(f92,plain,(
    ! [X0] : k1_yellow_1(X0) = k1_wellord2(X0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] : k1_yellow_1(X0) = k1_wellord2(X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow_1__t25_yellow_1.p',redefinition_k1_yellow_1)).

fof(f98,plain,(
    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k1_yellow_1(X0),X0)
      & v8_relat_2(k1_yellow_1(X0))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_1__t25_yellow_1.p',dt_k1_yellow_1)).

fof(f3095,plain,(
    ! [X0] :
      ( u1_struct_0(g1_orders_2(X0,k1_wellord2(X0))) = X0
      | ~ m1_subset_1(k1_wellord2(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(equality_resolution,[],[f1825])).

fof(f1825,plain,(
    ! [X6,X8,X7] :
      ( g1_orders_2(X7,X8) != g1_orders_2(X6,k1_wellord2(X6))
      | u1_struct_0(g1_orders_2(X6,k1_wellord2(X6))) = X7
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,X7))) ) ),
    inference(superposition,[],[f119,f172])).

fof(f172,plain,(
    ! [X0] : g1_orders_2(X0,k1_wellord2(X0)) = g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_wellord2(X0))),u1_orders_2(g1_orders_2(X0,k1_wellord2(X0)))) ),
    inference(subsumption_resolution,[],[f170,f141])).

fof(f141,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_wellord2(X0))) ),
    inference(definition_unfolding,[],[f100,f133])).

fof(f133,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_wellord2(X0)) ),
    inference(definition_unfolding,[],[f93,f92])).

fof(f93,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/yellow_1__t25_yellow_1.p',d1_yellow_1)).

fof(f100,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_1__t25_yellow_1.p',dt_k2_yellow_1)).

fof(f170,plain,(
    ! [X0] :
      ( g1_orders_2(X0,k1_wellord2(X0)) = g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_wellord2(X0))),u1_orders_2(g1_orders_2(X0,k1_wellord2(X0))))
      | ~ l1_orders_2(g1_orders_2(X0,k1_wellord2(X0))) ) ),
    inference(resolution,[],[f112,f142])).

fof(f142,plain,(
    ! [X0] : v1_orders_2(g1_orders_2(X0,k1_wellord2(X0))) ),
    inference(definition_unfolding,[],[f99,f133])).

fof(f99,plain,(
    ! [X0] : v1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f112,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_1__t25_yellow_1.p',abstractness_v1_orders_2)).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_1__t25_yellow_1.p',free_g1_orders_2)).

fof(f154,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_pre_topc(sK0),k1_wellord2(u1_pre_topc(sK0))))))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl8_3
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_pre_topc(sK0),k1_wellord2(u1_pre_topc(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f5281,plain,
    ( r1_tarski(sK1,u1_pre_topc(sK0))
    | ~ spl8_0
    | ~ spl8_3 ),
    inference(resolution,[],[f5161,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f75,f76])).

fof(f76,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_1__t25_yellow_1.p',d3_tarski)).

fof(f5161,plain,
    ( r2_hidden(sK4(sK1,u1_pre_topc(sK0)),u1_pre_topc(sK0))
    | ~ spl8_0
    | ~ spl8_3 ),
    inference(resolution,[],[f5106,f5110])).

fof(f5110,plain,
    ( r2_hidden(sK4(sK1,u1_pre_topc(sK0)),sK1)
    | ~ spl8_3 ),
    inference(resolution,[],[f5107,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f5106,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,u1_pre_topc(sK0)) )
    | ~ spl8_0 ),
    inference(subsumption_resolution,[],[f5105,f87])).

fof(f87,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0)))))
      | ~ v1_tops_2(sK1,sK0) )
    & ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0)))))
      | v1_tops_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f63,f65,f64])).

fof(f64,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
              | ~ v1_tops_2(X1,X0) )
            & ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
              | v1_tops_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0)))))
            | ~ v1_tops_2(X1,sK0) )
          & ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0)))))
            | v1_tops_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
            | ~ v1_tops_2(X1,X0) )
          & ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
          | ~ v1_tops_2(sK1,X0) )
        & ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
          | v1_tops_2(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
            | ~ v1_tops_2(X1,X0) )
          & ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
            | ~ v1_tops_2(X1,X0) )
          & ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_2(X1,X0)
          <~> m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_2(X1,X0)
          <~> m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v1_tops_2(X1,X0)
            <=> m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_1__t25_yellow_1.p',t25_yellow_1)).

fof(f5105,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,u1_pre_topc(sK0)) )
    | ~ spl8_0 ),
    inference(resolution,[],[f145,f1628])).

fof(f1628,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r2_hidden(X1,X0)
      | r2_hidden(X1,u1_pre_topc(sK0)) ) ),
    inference(subsumption_resolution,[],[f1627,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_1__t25_yellow_1.p',t4_subset)).

fof(f1627,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r2_hidden(X1,X0)
      | r2_hidden(X1,u1_pre_topc(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f1625,f86])).

fof(f86,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f1625,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r2_hidden(X1,X0)
      | r2_hidden(X1,u1_pre_topc(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f1508,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_1__t25_yellow_1.p',d5_pre_topc)).

fof(f1508,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X0,sK0)
      | ~ v1_tops_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f1417,f86])).

fof(f1417,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X3,X1)
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v3_pre_topc(X3,X0) ) ),
    inference(subsumption_resolution,[],[f105,f128])).

fof(f105,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK2(X0,X1),X0)
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f69,f70])).

fof(f70,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
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
    inference(rectify,[],[f68])).

fof(f68,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_1__t25_yellow_1.p',d1_tops_2)).

fof(f145,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl8_0
  <=> v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f5102,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_82 ),
    inference(avatar_contradiction_clause,[],[f5101])).

fof(f5101,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_82 ),
    inference(subsumption_resolution,[],[f5100,f148])).

fof(f148,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl8_1
  <=> ~ v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f5100,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ spl8_2
    | ~ spl8_82 ),
    inference(subsumption_resolution,[],[f5099,f86])).

fof(f5099,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_tops_2(sK1,sK0)
    | ~ spl8_2
    | ~ spl8_82 ),
    inference(subsumption_resolution,[],[f5092,f87])).

fof(f5092,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | v1_tops_2(sK1,sK0)
    | ~ spl8_2
    | ~ spl8_82 ),
    inference(resolution,[],[f5009,f2016])).

fof(f2016,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X1,X0),u1_pre_topc(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | v1_tops_2(X0,X1) ) ),
    inference(subsumption_resolution,[],[f953,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f953,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ r2_hidden(sK2(X1,X0),u1_pre_topc(X1))
      | ~ m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(duplicate_literal_removal,[],[f952])).

fof(f952,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ r2_hidden(sK2(X1,X0),u1_pre_topc(X1))
      | ~ m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f108,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(sK2(X0,X1),X0)
      | v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f5009,plain,
    ( r2_hidden(sK2(sK0,sK1),u1_pre_topc(sK0))
    | ~ spl8_2
    | ~ spl8_82 ),
    inference(resolution,[],[f4981,f873])).

fof(f873,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X2))
        | r2_hidden(sK2(sK0,sK1),X2) )
    | ~ spl8_82 ),
    inference(resolution,[],[f780,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f780,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK1,X1)
        | r2_hidden(sK2(sK0,sK1),X1) )
    | ~ spl8_82 ),
    inference(resolution,[],[f770,f121])).

fof(f121,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f770,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | ~ spl8_82 ),
    inference(avatar_component_clause,[],[f769])).

fof(f769,plain,
    ( spl8_82
  <=> r2_hidden(sK2(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_82])])).

fof(f4981,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_pre_topc(sK0)))
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f3096,f151])).

fof(f151,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_pre_topc(sK0),k1_wellord2(u1_pre_topc(sK0))))))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl8_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_pre_topc(sK0),k1_wellord2(u1_pre_topc(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f777,plain,(
    spl8_81 ),
    inference(avatar_contradiction_clause,[],[f776])).

fof(f776,plain,
    ( $false
    | ~ spl8_81 ),
    inference(subsumption_resolution,[],[f764,f87])).

fof(f764,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl8_81 ),
    inference(avatar_component_clause,[],[f763])).

fof(f763,plain,
    ( spl8_81
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_81])])).

fof(f771,plain,
    ( ~ spl8_81
    | spl8_82
    | spl8_1 ),
    inference(avatar_split_clause,[],[f758,f147,f769,f763])).

fof(f758,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f757,f86])).

fof(f757,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_1 ),
    inference(resolution,[],[f148,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f156,plain,
    ( spl8_0
    | spl8_2 ),
    inference(avatar_split_clause,[],[f135,f150,f144])).

fof(f135,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_pre_topc(sK0),k1_wellord2(u1_pre_topc(sK0))))))
    | v1_tops_2(sK1,sK0) ),
    inference(definition_unfolding,[],[f88,f133])).

fof(f88,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0)))))
    | v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f155,plain,
    ( ~ spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f134,f153,f147])).

fof(f134,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_pre_topc(sK0),k1_wellord2(u1_pre_topc(sK0))))))
    | ~ v1_tops_2(sK1,sK0) ),
    inference(definition_unfolding,[],[f89,f133])).

fof(f89,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0)))))
    | ~ v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f66])).
%------------------------------------------------------------------------------
