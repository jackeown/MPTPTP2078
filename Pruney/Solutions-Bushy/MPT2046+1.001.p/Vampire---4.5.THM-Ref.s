%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2046+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 168 expanded)
%              Number of leaves         :   23 (  62 expanded)
%              Depth                    :   17
%              Number of atoms          :  324 ( 588 expanded)
%              Number of equality atoms :   23 (  23 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f183,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f100,f118,f120,f127,f138,f148,f150,f182])).

fof(f182,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | spl3_7 ),
    inference(resolution,[],[f178,f142])).

fof(f142,plain,
    ( ~ m1_subset_1(k1_yellow19(sK0,sK1),k1_zfmisc_1(k1_yellow19(sK0,sK1)))
    | spl3_7 ),
    inference(resolution,[],[f117,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f117,plain,
    ( ~ r1_tarski(k1_yellow19(sK0,sK1),k1_yellow19(sK0,sK1))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl3_7
  <=> r1_tarski(k1_yellow19(sK0,sK1),k1_yellow19(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f178,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f177,f50])).

fof(f50,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f8,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f177,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2(k1_zfmisc_1(k2_zfmisc_1(X0,X0))),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | m1_subset_1(X0,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f176,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( l1_orders_2(g1_orders_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_orders_2)).

fof(f176,plain,(
    ! [X0] :
      ( ~ l1_orders_2(g1_orders_2(X0,sK2(k1_zfmisc_1(k2_zfmisc_1(X0,X0)))))
      | m1_subset_1(X0,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f171,f45])).

fof(f45,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f171,plain,(
    ! [X2] :
      ( ~ l1_struct_0(g1_orders_2(X2,sK2(k1_zfmisc_1(k2_zfmisc_1(X2,X2)))))
      | m1_subset_1(X2,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f63,f156])).

fof(f156,plain,(
    ! [X0] : u1_struct_0(g1_orders_2(X0,sK2(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))) = X0 ),
    inference(resolution,[],[f153,f50])).

fof(f153,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2(k1_zfmisc_1(k2_zfmisc_1(X0,X0))),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | u1_struct_0(g1_orders_2(X0,sK2(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))) = X0 ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X6,X7,X5] :
      ( g1_orders_2(X5,sK2(k1_zfmisc_1(k2_zfmisc_1(X5,X5)))) != g1_orders_2(X6,X7)
      | u1_struct_0(g1_orders_2(X5,sK2(k1_zfmisc_1(k2_zfmisc_1(X5,X5))))) = X6
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))) ) ),
    inference(superposition,[],[f53,f75])).

fof(f75,plain,(
    ! [X3] : g1_orders_2(X3,sK2(k1_zfmisc_1(k2_zfmisc_1(X3,X3)))) = g1_orders_2(u1_struct_0(g1_orders_2(X3,sK2(k1_zfmisc_1(k2_zfmisc_1(X3,X3))))),u1_orders_2(g1_orders_2(X3,sK2(k1_zfmisc_1(k2_zfmisc_1(X3,X3)))))) ),
    inference(resolution,[],[f72,f50])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) = g1_orders_2(u1_struct_0(g1_orders_2(X0,X1)),u1_orders_2(g1_orders_2(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) = g1_orders_2(u1_struct_0(g1_orders_2(X0,X1)),u1_orders_2(g1_orders_2(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(resolution,[],[f64,f52])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(g1_orders_2(X0,X1))
      | g1_orders_2(X0,X1) = g1_orders_2(u1_struct_0(g1_orders_2(X0,X1)),u1_orders_2(g1_orders_2(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(resolution,[],[f47,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_orders_2(g1_orders_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f63,plain,(
    ! [X0] :
      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f44,f43])).

fof(f43,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f44,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f150,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl3_1 ),
    inference(resolution,[],[f90,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ r2_waybel_7(sK0,k1_yellow19(sK0,sK1),sK1)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_waybel_7(X0,k1_yellow19(X0,X1),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r2_waybel_7(sK0,k1_yellow19(sK0,X1),X1)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ~ r2_waybel_7(sK0,k1_yellow19(sK0,X1),X1)
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ~ r2_waybel_7(sK0,k1_yellow19(sK0,sK1),sK1)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_waybel_7(X0,k1_yellow19(X0,X1),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_waybel_7(X0,k1_yellow19(X0,X1),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r2_waybel_7(X0,k1_yellow19(X0,X1),X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_waybel_7(X0,k1_yellow19(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_yellow19)).

fof(f90,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f148,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_8
    | ~ spl3_6
    | spl3_4 ),
    inference(avatar_split_clause,[],[f145,f103,f111,f124,f92,f88])).

fof(f92,plain,
    ( spl3_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f124,plain,
    ( spl3_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f111,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f103,plain,
    ( spl3_4
  <=> m1_subset_1(k1_yellow19(sK0,sK1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f145,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_4 ),
    inference(resolution,[],[f105,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow19)).

fof(f105,plain,
    ( ~ m1_subset_1(k1_yellow19(sK0,sK1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f138,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl3_8 ),
    inference(resolution,[],[f126,f40])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f126,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f124])).

fof(f127,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_8
    | ~ spl3_6
    | spl3_5 ),
    inference(avatar_split_clause,[],[f121,f107,f111,f124,f92,f88])).

fof(f107,plain,
    ( spl3_5
  <=> v13_waybel_0(k1_yellow19(sK0,sK1),k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f121,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_5 ),
    inference(resolution,[],[f109,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k1_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(k1_yellow19(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k1_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(k1_yellow19(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k1_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(k1_yellow19(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_yellow19)).

fof(f109,plain,
    ( ~ v13_waybel_0(k1_yellow19(sK0,sK1),k3_yellow_1(k2_struct_0(sK0)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f120,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f113,f41])).

fof(f41,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f113,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f111])).

fof(f118,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f101,f96,f115,f111,f107,f103])).

fof(f96,plain,
    ( spl3_3
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k1_yellow19(sK0,X0),X1)
        | r2_waybel_7(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f101,plain,
    ( ~ r1_tarski(k1_yellow19(sK0,sK1),k1_yellow19(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v13_waybel_0(k1_yellow19(sK0,sK1),k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(k1_yellow19(sK0,sK1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl3_3 ),
    inference(resolution,[],[f97,f42])).

% (6770)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (6755)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f42,plain,(
    ~ r2_waybel_7(sK0,k1_yellow19(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( r2_waybel_7(sK0,X1,X0)
        | ~ r1_tarski(k1_yellow19(sK0,X0),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f100,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | spl3_2 ),
    inference(resolution,[],[f94,f39])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f94,plain,
    ( ~ v2_pre_topc(sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f98,plain,
    ( spl3_1
    | ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f86,f96,f92,f88])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_yellow19(sK0,X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_waybel_7(sK0,X1,X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f49,f40])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(k1_yellow19(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_waybel_7(X0,X2,X1)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_waybel_7(X0,X2,X1)
                  | ~ r1_tarski(k1_yellow19(X0,X1),X2) )
                & ( r1_tarski(k1_yellow19(X0,X1),X2)
                  | ~ r2_waybel_7(X0,X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_7(X0,X2,X1)
              <=> r1_tarski(k1_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_7(X0,X2,X1)
              <=> r1_tarski(k1_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
             => ( r2_waybel_7(X0,X2,X1)
              <=> r1_tarski(k1_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow19)).

%------------------------------------------------------------------------------
