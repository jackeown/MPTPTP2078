%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:32 EST 2020

% Result     : Theorem 3.26s
% Output     : Refutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :  290 (2870 expanded)
%              Number of leaves         :   37 ( 842 expanded)
%              Depth                    :   34
%              Number of atoms          : 1363 (8996 expanded)
%              Number of equality atoms :   33 (1844 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2690,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f216,f336,f1383,f1403,f1408,f1426,f1495,f1515,f1520,f1584,f1597,f1677,f1743,f2689])).

fof(f2689,plain,
    ( spl5_1
    | spl5_5
    | ~ spl5_13
    | ~ spl5_18
    | ~ spl5_19
    | spl5_29 ),
    inference(avatar_contradiction_clause,[],[f2688])).

fof(f2688,plain,
    ( $false
    | spl5_1
    | spl5_5
    | ~ spl5_13
    | ~ spl5_18
    | ~ spl5_19
    | spl5_29 ),
    inference(subsumption_resolution,[],[f2687,f1477])).

fof(f1477,plain,
    ( m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f1476])).

fof(f1476,plain,
    ( spl5_13
  <=> m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f2687,plain,
    ( ~ m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK0)
    | spl5_1
    | spl5_5
    | ~ spl5_13
    | ~ spl5_18
    | ~ spl5_19
    | spl5_29 ),
    inference(subsumption_resolution,[],[f2686,f148])).

fof(f148,plain,(
    m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) ),
    inference(resolution,[],[f143,f104])).

fof(f104,plain,(
    ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f61,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_yellow_1)).

fof(f60,plain,(
    ~ v2_lattice3(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ~ v2_lattice3(k2_yellow_1(sK0))
    & ! [X1,X2] :
        ( r2_hidden(k3_xboole_0(X1,X2),sK0)
        | ~ r2_hidden(X2,sK0)
        | ~ r2_hidden(X1,sK0) )
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f44])).

fof(f44,plain,
    ( ? [X0] :
        ( ~ v2_lattice3(k2_yellow_1(X0))
        & ! [X1,X2] :
            ( r2_hidden(k3_xboole_0(X1,X2),X0)
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ~ v2_lattice3(k2_yellow_1(sK0))
      & ! [X2,X1] :
          ( r2_hidden(k3_xboole_0(X1,X2),sK0)
          | ~ r2_hidden(X2,sK0)
          | ~ r2_hidden(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ~ v2_lattice3(k2_yellow_1(X0))
      & ! [X1,X2] :
          ( r2_hidden(k3_xboole_0(X1,X2),X0)
          | ~ r2_hidden(X2,X0)
          | ~ r2_hidden(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ~ v2_lattice3(k2_yellow_1(X0))
      & ! [X1,X2] :
          ( r2_hidden(k3_xboole_0(X1,X2),X0)
          | ~ r2_hidden(X2,X0)
          | ~ r2_hidden(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( ! [X1,X2] :
              ( ( r2_hidden(X2,X0)
                & r2_hidden(X1,X0) )
             => r2_hidden(k3_xboole_0(X1,X2),X0) )
         => v2_lattice3(k2_yellow_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( ! [X1,X2] :
            ( ( r2_hidden(X2,X0)
              & r2_hidden(X1,X0) )
           => r2_hidden(k3_xboole_0(X1,X2),X0) )
       => v2_lattice3(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow_1)).

fof(f143,plain,(
    ! [X2] :
      ( v2_lattice3(g1_orders_2(X2,k1_yellow_1(X2)))
      | m1_subset_1(sK2(g1_orders_2(X2,k1_yellow_1(X2))),X2) ) ),
    inference(subsumption_resolution,[],[f142,f105])).

fof(f105,plain,(
    ! [X0] : v5_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f70,f61])).

fof(f70,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f142,plain,(
    ! [X2] :
      ( m1_subset_1(sK2(g1_orders_2(X2,k1_yellow_1(X2))),X2)
      | v2_lattice3(g1_orders_2(X2,k1_yellow_1(X2)))
      | ~ v5_orders_2(g1_orders_2(X2,k1_yellow_1(X2))) ) ),
    inference(subsumption_resolution,[],[f137,f109])).

fof(f109,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f72,f61])).

fof(f72,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f137,plain,(
    ! [X2] :
      ( m1_subset_1(sK2(g1_orders_2(X2,k1_yellow_1(X2))),X2)
      | v2_lattice3(g1_orders_2(X2,k1_yellow_1(X2)))
      | ~ l1_orders_2(g1_orders_2(X2,k1_yellow_1(X2)))
      | ~ v5_orders_2(g1_orders_2(X2,k1_yellow_1(X2))) ) ),
    inference(superposition,[],[f87,f135])).

fof(f135,plain,(
    ! [X0] : u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X0 ),
    inference(equality_resolution,[],[f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,k1_yellow_1(X1))
      | u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X1 ) ),
    inference(subsumption_resolution,[],[f128,f109])).

fof(f128,plain,(
    ! [X0,X1] :
      ( u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X1
      | g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,k1_yellow_1(X1))
      | ~ l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ) ),
    inference(resolution,[],[f126,f108])).

fof(f108,plain,(
    ! [X0] : v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f67,f61])).

fof(f67,plain,(
    ! [X0] : v1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ v1_orders_2(X0)
      | u1_struct_0(X0) = X1
      | g1_orders_2(X1,k1_yellow_1(X1)) != X0
      | ~ l1_orders_2(X0) ) ),
    inference(superposition,[],[f125,f78])).

fof(f78,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2)
      | X0 = X1 ) ),
    inference(resolution,[],[f98,f66])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k1_yellow_1(X0),X0)
      & v8_relat_2(k1_yellow_1(X0))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_1)).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f87,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),u1_struct_0(X0))
      | v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ( ~ r2_yellow_0(X0,k2_tarski(sK1(X0),sK2(X0)))
            & m1_subset_1(sK2(X0),u1_struct_0(X0))
            & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r2_yellow_0(X0,k2_tarski(X3,X4))
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v2_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f48,f50,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ r2_yellow_0(X0,k2_tarski(sK1(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ~ r2_yellow_0(X0,k2_tarski(sK1(X0),X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r2_yellow_0(X0,k2_tarski(sK1(X0),sK2(X0)))
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r2_yellow_0(X0,k2_tarski(X3,X4))
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v2_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( r2_yellow_0(X0,k2_tarski(X1,X2))
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v2_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( r2_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( r2_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v2_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r2_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_yellow_0)).

fof(f2686,plain,
    ( ~ m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | ~ m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK0)
    | spl5_1
    | spl5_5
    | ~ spl5_13
    | ~ spl5_18
    | ~ spl5_19
    | spl5_29 ),
    inference(subsumption_resolution,[],[f2684,f1676])).

fof(f1676,plain,
    ( ~ r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | spl5_29 ),
    inference(avatar_component_clause,[],[f1674])).

fof(f1674,plain,
    ( spl5_29
  <=> r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f2684,plain,
    ( r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | ~ m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK0)
    | spl5_1
    | spl5_5
    | ~ spl5_13
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(resolution,[],[f1968,f229])).

fof(f229,plain,(
    ! [X0,X1] :
      ( ~ r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0)
      | r1_tarski(X1,X0)
      | ~ m1_subset_1(X0,sK0)
      | ~ m1_subset_1(X1,sK0) ) ),
    inference(resolution,[],[f228,f58])).

fof(f58,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f228,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0)
      | r1_tarski(X1,X2)
      | ~ r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(forward_demodulation,[],[f227,f135])).

fof(f227,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r1_tarski(X1,X2)
      | ~ r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f115,f135])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f76,f61,f61,f61])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
                  | ~ r1_tarski(X1,X2) )
                & ( r1_tarski(X1,X2)
                  | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f1968,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | spl5_1
    | spl5_5
    | ~ spl5_13
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f1967,f1477])).

fof(f1967,plain,
    ( ~ m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK0)
    | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | spl5_1
    | spl5_5
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f1966,f135])).

fof(f1966,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | spl5_1
    | spl5_5
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f1965,f148])).

fof(f1965,plain,
    ( ~ m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | spl5_1
    | spl5_5
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f1964,f135])).

fof(f1964,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | spl5_1
    | spl5_5
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f1963,f211])).

fof(f211,plain,
    ( ~ v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl5_1
  <=> v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1963,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | spl5_5
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f1962,f107])).

fof(f107,plain,(
    ! [X0] : v3_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f68,f61])).

fof(f68,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f1962,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | spl5_5
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f1955,f109])).

fof(f1955,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | spl5_5
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(resolution,[],[f1644,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f1644,plain,
    ( r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | spl5_5
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f1643,f1509])).

fof(f1509,plain,
    ( m1_subset_1(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f1508])).

fof(f1508,plain,
    ( spl5_18
  <=> m1_subset_1(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f1643,plain,
    ( r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0)
    | spl5_5
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f1642,f701])).

fof(f701,plain,
    ( ~ r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f700])).

fof(f700,plain,
    ( spl5_5
  <=> r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f1642,plain,
    ( r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))))
    | ~ m1_subset_1(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0)
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f1641,f148])).

fof(f1641,plain,
    ( ~ m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))))
    | ~ m1_subset_1(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0)
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f1624,f149])).

fof(f149,plain,(
    m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) ),
    inference(resolution,[],[f145,f104])).

fof(f145,plain,(
    ! [X3] :
      ( v2_lattice3(g1_orders_2(X3,k1_yellow_1(X3)))
      | m1_subset_1(sK1(g1_orders_2(X3,k1_yellow_1(X3))),X3) ) ),
    inference(subsumption_resolution,[],[f144,f105])).

fof(f144,plain,(
    ! [X3] :
      ( m1_subset_1(sK1(g1_orders_2(X3,k1_yellow_1(X3))),X3)
      | v2_lattice3(g1_orders_2(X3,k1_yellow_1(X3)))
      | ~ v5_orders_2(g1_orders_2(X3,k1_yellow_1(X3))) ) ),
    inference(subsumption_resolution,[],[f138,f109])).

fof(f138,plain,(
    ! [X3] :
      ( m1_subset_1(sK1(g1_orders_2(X3,k1_yellow_1(X3))),X3)
      | v2_lattice3(g1_orders_2(X3,k1_yellow_1(X3)))
      | ~ l1_orders_2(g1_orders_2(X3,k1_yellow_1(X3)))
      | ~ v5_orders_2(g1_orders_2(X3,k1_yellow_1(X3))) ) ),
    inference(superposition,[],[f86,f135])).

fof(f86,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),u1_struct_0(X0))
      | v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1624,plain,
    ( ~ m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | ~ m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))))
    | ~ m1_subset_1(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0)
    | ~ spl5_19 ),
    inference(resolution,[],[f1513,f524])).

fof(f524,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r1_lattice3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6)
      | ~ m1_subset_1(X3,X4)
      | ~ m1_subset_1(X5,X4)
      | r1_orders_2(g1_orders_2(X4,k1_yellow_1(X4)),sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X5)
      | r2_yellow_0(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5))
      | ~ m1_subset_1(X6,X4) ) ),
    inference(subsumption_resolution,[],[f196,f172])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2),X0)
      | r2_yellow_0(g1_orders_2(X0,k1_yellow_1(X0)),X1)
      | ~ r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(subsumption_resolution,[],[f171,f105])).

fof(f171,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2),X0)
      | r2_yellow_0(g1_orders_2(X0,k1_yellow_1(X0)),X1)
      | ~ r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ v5_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ) ),
    inference(subsumption_resolution,[],[f170,f109])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2),X0)
      | r2_yellow_0(g1_orders_2(X0,k1_yellow_1(X0)),X1)
      | ~ r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))
      | ~ v5_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ) ),
    inference(superposition,[],[f92,f135])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
                  & r1_lattice3(X0,X1,sK3(X0,X1,X2))
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,X5,sK4(X0,X1))
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,sK4(X0,X1))
              & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f53,f55,f54])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X5,X4)
              | ~ r1_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,X5,sK4(X0,X1))
            | ~ r1_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK4(X0,X1))
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X5,X4)
                    | ~ r1_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X3,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow_0)).

fof(f196,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ m1_subset_1(X6,X4)
      | ~ m1_subset_1(X3,X4)
      | ~ m1_subset_1(X5,X4)
      | ~ m1_subset_1(sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X4)
      | r1_orders_2(g1_orders_2(X4,k1_yellow_1(X4)),sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X5)
      | r2_yellow_0(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5))
      | ~ r1_lattice3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6) ) ),
    inference(forward_demodulation,[],[f195,f135])).

fof(f195,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ m1_subset_1(X3,X4)
      | ~ m1_subset_1(X5,X4)
      | ~ m1_subset_1(sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X4)
      | r1_orders_2(g1_orders_2(X4,k1_yellow_1(X4)),sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X5)
      | r2_yellow_0(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5))
      | ~ r1_lattice3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(g1_orders_2(X4,k1_yellow_1(X4)))) ) ),
    inference(subsumption_resolution,[],[f194,f105])).

fof(f194,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ m1_subset_1(X3,X4)
      | ~ m1_subset_1(X5,X4)
      | ~ m1_subset_1(sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X4)
      | r1_orders_2(g1_orders_2(X4,k1_yellow_1(X4)),sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X5)
      | r2_yellow_0(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5))
      | ~ r1_lattice3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(g1_orders_2(X4,k1_yellow_1(X4))))
      | ~ v5_orders_2(g1_orders_2(X4,k1_yellow_1(X4))) ) ),
    inference(subsumption_resolution,[],[f190,f109])).

fof(f190,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ m1_subset_1(X3,X4)
      | ~ m1_subset_1(X5,X4)
      | ~ m1_subset_1(sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X4)
      | r1_orders_2(g1_orders_2(X4,k1_yellow_1(X4)),sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X5)
      | r2_yellow_0(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5))
      | ~ r1_lattice3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(g1_orders_2(X4,k1_yellow_1(X4))))
      | ~ l1_orders_2(g1_orders_2(X4,k1_yellow_1(X4)))
      | ~ v5_orders_2(g1_orders_2(X4,k1_yellow_1(X4))) ) ),
    inference(resolution,[],[f180,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f180,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),k2_tarski(X1,X2),X3)
      | ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X3,X0)
      | r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X3,X2) ) ),
    inference(forward_demodulation,[],[f179,f135])).

fof(f179,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),k2_tarski(X1,X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X3,X2) ) ),
    inference(forward_demodulation,[],[f178,f135])).

fof(f178,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,X0)
      | ~ r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),k2_tarski(X1,X2),X3)
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X3,X2) ) ),
    inference(forward_demodulation,[],[f177,f135])).

fof(f177,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),k2_tarski(X1,X2),X3)
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X3,X2) ) ),
    inference(resolution,[],[f80,f109])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X3,X1)
                      | ~ r1_orders_2(X0,X2,X1) )
                    & ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ~ r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X3,X1)
                      | ~ r1_orders_2(X0,X2,X1) )
                    & ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ~ r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                     => r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                     => ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) ) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                     => r1_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                     => ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_yellow_0)).

fof(f1513,plain,
    ( r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f1512])).

fof(f1512,plain,
    ( spl5_19
  <=> r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f1743,plain,
    ( ~ spl5_13
    | ~ spl5_15
    | spl5_28 ),
    inference(avatar_contradiction_clause,[],[f1742])).

fof(f1742,plain,
    ( $false
    | ~ spl5_13
    | ~ spl5_15
    | spl5_28 ),
    inference(subsumption_resolution,[],[f1741,f1477])).

fof(f1741,plain,
    ( ~ m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK0)
    | ~ spl5_15
    | spl5_28 ),
    inference(subsumption_resolution,[],[f1740,f149])).

fof(f1740,plain,
    ( ~ m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | ~ m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK0)
    | ~ spl5_15
    | spl5_28 ),
    inference(subsumption_resolution,[],[f1738,f1672])).

fof(f1672,plain,
    ( ~ r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | spl5_28 ),
    inference(avatar_component_clause,[],[f1670])).

fof(f1670,plain,
    ( spl5_28
  <=> r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f1738,plain,
    ( r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | ~ m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK0)
    | ~ spl5_15 ),
    inference(resolution,[],[f1494,f229])).

fof(f1494,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f1492])).

fof(f1492,plain,
    ( spl5_15
  <=> r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f1677,plain,
    ( ~ spl5_28
    | ~ spl5_29
    | ~ spl5_2
    | spl5_5
    | ~ spl5_9
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f1668,f1512,f1380,f700,f214,f1674,f1670])).

fof(f214,plain,
    ( spl5_2
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,sK0)
        | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0)
        | ~ r1_tarski(X1,X0)
        | ~ m1_subset_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1380,plain,
    ( spl5_9
  <=> r2_hidden(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f1668,plain,
    ( ~ r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ spl5_2
    | spl5_5
    | ~ spl5_9
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f1667,f148])).

fof(f1667,plain,
    ( ~ m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | ~ r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ spl5_2
    | spl5_5
    | ~ spl5_9
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f1666,f701])).

fof(f1666,plain,
    ( r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))))
    | ~ m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | ~ r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ spl5_2
    | ~ spl5_9
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f1665,f1381])).

fof(f1381,plain,
    ( r2_hidden(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f1380])).

fof(f1665,plain,
    ( ~ r2_hidden(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0)
    | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))))
    | ~ m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | ~ r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ spl5_2
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f1630,f149])).

fof(f1630,plain,
    ( ~ m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | ~ r2_hidden(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0)
    | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))))
    | ~ m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | ~ r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ spl5_2
    | ~ spl5_19 ),
    inference(resolution,[],[f1513,f252])).

fof(f252,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,k3_xboole_0(X1,X0))
        | ~ m1_subset_1(X1,sK0)
        | ~ r2_hidden(k3_xboole_0(X1,X0),sK0)
        | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),X2)
        | ~ m1_subset_1(X0,sK0)
        | ~ r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,k3_xboole_0(X1,X0)),X0)
        | ~ r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,k3_xboole_0(X1,X0)),X1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f251,f224])).

fof(f224,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k3_xboole_0(X0,X1),sK0)
        | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),X2)
        | ~ r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,k3_xboole_0(X0,X1))
        | ~ r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,k3_xboole_0(X0,X1)),X1)
        | ~ r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,k3_xboole_0(X0,X1)),X0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f223,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f223,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),X1)
        | ~ m1_subset_1(X1,sK0)
        | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),X0)
        | ~ r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) )
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f222])).

fof(f222,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,sK0)
        | ~ r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),X1)
        | ~ m1_subset_1(X1,sK0)
        | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),X0)
        | ~ r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) )
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f221,f135])).

fof(f221,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),X1)
        | ~ m1_subset_1(X1,sK0)
        | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),X0)
        | ~ r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f220,f172])).

fof(f220,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),sK0)
        | ~ r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),X1)
        | ~ m1_subset_1(X1,sK0)
        | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),X0)
        | ~ r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f219,f105])).

fof(f219,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),sK0)
        | ~ r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),X1)
        | ~ m1_subset_1(X1,sK0)
        | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),X0)
        | ~ r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
        | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f217,f109])).

fof(f217,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),sK0)
        | ~ r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),X1)
        | ~ m1_subset_1(X1,sK0)
        | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),X0)
        | ~ r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
        | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
        | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) )
    | ~ spl5_2 ),
    inference(resolution,[],[f215,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f215,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0)
        | ~ m1_subset_1(X1,sK0)
        | ~ r1_tarski(X1,X0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f214])).

fof(f251,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k3_xboole_0(X2,X3),sK0)
      | ~ m1_subset_1(X3,sK0)
      | ~ m1_subset_1(X2,sK0)
      | ~ r2_hidden(k3_xboole_0(X2,X3),sK0) ) ),
    inference(duplicate_literal_removal,[],[f250])).

fof(f250,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,sK0)
      | ~ m1_subset_1(X3,sK0)
      | m1_subset_1(k3_xboole_0(X2,X3),sK0)
      | ~ r2_hidden(k3_xboole_0(X2,X3),sK0)
      | ~ m1_subset_1(X2,sK0) ) ),
    inference(forward_demodulation,[],[f249,f135])).

fof(f249,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,sK0)
      | m1_subset_1(k3_xboole_0(X2,X3),sK0)
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ r2_hidden(k3_xboole_0(X2,X3),sK0)
      | ~ m1_subset_1(X2,sK0) ) ),
    inference(duplicate_literal_removal,[],[f248])).

fof(f248,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,sK0)
      | m1_subset_1(k3_xboole_0(X2,X3),sK0)
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(k3_xboole_0(X2,X3),sK0)
      | ~ m1_subset_1(X2,sK0) ) ),
    inference(forward_demodulation,[],[f247,f135])).

fof(f247,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k3_xboole_0(X2,X3),sK0)
      | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(k3_xboole_0(X2,X3),sK0)
      | ~ m1_subset_1(X2,sK0) ) ),
    inference(forward_demodulation,[],[f246,f135])).

fof(f246,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(k3_xboole_0(X2,X3),sK0)
      | ~ m1_subset_1(X2,sK0) ) ),
    inference(subsumption_resolution,[],[f244,f109])).

fof(f244,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(k3_xboole_0(X2,X3),sK0)
      | ~ m1_subset_1(X2,sK0) ) ),
    inference(superposition,[],[f102,f242])).

fof(f242,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,X0) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0)
      | ~ m1_subset_1(X0,sK0)
      | ~ r2_hidden(k3_xboole_0(X1,X0),sK0)
      | ~ m1_subset_1(X1,sK0) ) ),
    inference(resolution,[],[f241,f58])).

fof(f241,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0)
      | k3_xboole_0(X1,X2) = k11_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
      | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(forward_demodulation,[],[f240,f135])).

fof(f240,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | k3_xboole_0(X1,X2) = k11_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
      | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f113,f135])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k11_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
      | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f75,f61,f61,f61])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r2_hidden(k3_xboole_0(X1,X2),X0)
               => k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_1)).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(f1597,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f1596])).

fof(f1596,plain,
    ( $false
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f1595,f105])).

fof(f1595,plain,
    ( ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f1594,f109])).

fof(f1594,plain,
    ( ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f1588,f104])).

fof(f1588,plain,
    ( v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl5_5 ),
    inference(resolution,[],[f702,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(X0,k2_tarski(sK1(X0),sK2(X0)))
      | v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f702,plain,
    ( r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f700])).

fof(f1584,plain,
    ( ~ spl5_2
    | ~ spl5_18
    | spl5_19 ),
    inference(avatar_contradiction_clause,[],[f1583])).

fof(f1583,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_18
    | spl5_19 ),
    inference(subsumption_resolution,[],[f1582,f117])).

fof(f117,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f95,f96])).

fof(f96,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f95,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1582,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ spl5_2
    | ~ spl5_18
    | spl5_19 ),
    inference(subsumption_resolution,[],[f1581,f95])).

fof(f1581,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ r1_tarski(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ spl5_2
    | ~ spl5_18
    | spl5_19 ),
    inference(subsumption_resolution,[],[f1580,f148])).

fof(f1580,plain,
    ( ~ m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | ~ r1_tarski(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ r1_tarski(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ spl5_2
    | ~ spl5_18
    | spl5_19 ),
    inference(subsumption_resolution,[],[f1579,f1509])).

fof(f1579,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0)
    | ~ m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | ~ r1_tarski(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ r1_tarski(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ spl5_2
    | spl5_19 ),
    inference(subsumption_resolution,[],[f1578,f149])).

fof(f1578,plain,
    ( ~ m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | ~ m1_subset_1(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0)
    | ~ m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | ~ r1_tarski(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ r1_tarski(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ spl5_2
    | spl5_19 ),
    inference(resolution,[],[f1514,f258])).

fof(f258,plain,
    ( ! [X2,X0,X1] :
        ( r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(X1,X0),X2)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X2,sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X2,X0) )
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f257])).

fof(f257,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X2,sK0)
        | r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(X1,X0),X2)
        | ~ r1_tarski(X2,X1)
        | ~ m1_subset_1(X2,sK0)
        | ~ r1_tarski(X2,X0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f256,f215])).

fof(f256,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,X1)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X2,sK0)
        | r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(X0,X1),X2)
        | ~ r1_tarski(X2,X0) )
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f255])).

fof(f255,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,X1)
        | ~ m1_subset_1(X2,sK0)
        | r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(X0,X1),X2)
        | ~ m1_subset_1(X2,sK0)
        | ~ r1_tarski(X2,X0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f235,f215])).

fof(f235,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
      | ~ m1_subset_1(X1,X0)
      | r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),k2_tarski(X3,X2),X1) ) ),
    inference(forward_demodulation,[],[f234,f135])).

fof(f234,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
      | ~ r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X3)
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),k2_tarski(X3,X2),X1) ) ),
    inference(forward_demodulation,[],[f233,f135])).

fof(f233,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,X0)
      | ~ r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
      | ~ r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),k2_tarski(X3,X2),X1) ) ),
    inference(forward_demodulation,[],[f232,f135])).

fof(f232,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
      | ~ r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X3)
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),k2_tarski(X3,X2),X1) ) ),
    inference(resolution,[],[f81,f109])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_lattice3(X0,k2_tarski(X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1514,plain,
    ( ~ r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))))
    | spl5_19 ),
    inference(avatar_component_clause,[],[f1512])).

fof(f1520,plain,
    ( ~ spl5_9
    | spl5_18 ),
    inference(avatar_contradiction_clause,[],[f1519])).

fof(f1519,plain,
    ( $false
    | ~ spl5_9
    | spl5_18 ),
    inference(subsumption_resolution,[],[f1518,f1381])).

fof(f1518,plain,
    ( ~ r2_hidden(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0)
    | spl5_18 ),
    inference(subsumption_resolution,[],[f1517,f149])).

fof(f1517,plain,
    ( ~ m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | ~ r2_hidden(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0)
    | spl5_18 ),
    inference(subsumption_resolution,[],[f1516,f148])).

fof(f1516,plain,
    ( ~ m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | ~ m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | ~ r2_hidden(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0)
    | spl5_18 ),
    inference(resolution,[],[f1510,f251])).

fof(f1510,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f1508])).

fof(f1515,plain,
    ( ~ spl5_18
    | ~ spl5_19
    | spl5_5
    | spl5_13 ),
    inference(avatar_split_clause,[],[f1506,f1476,f700,f1512,f1508])).

fof(f1506,plain,
    ( r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))))
    | ~ r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))))
    | ~ m1_subset_1(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0)
    | spl5_13 ),
    inference(resolution,[],[f1478,f172])).

fof(f1478,plain,
    ( ~ m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK0)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f1476])).

fof(f1495,plain,
    ( spl5_15
    | ~ spl5_13
    | spl5_1
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1490,f1376,f210,f1476,f1492])).

fof(f1376,plain,
    ( spl5_8
  <=> r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f1490,plain,
    ( ~ m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK0)
    | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | spl5_1
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f1489,f135])).

fof(f1489,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | spl5_1
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f1488,f149])).

fof(f1488,plain,
    ( ~ m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | spl5_1
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f1487,f135])).

fof(f1487,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | spl5_1
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f1486,f211])).

fof(f1486,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f1485,f107])).

fof(f1485,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f1468,f109])).

fof(f1468,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl5_8 ),
    inference(resolution,[],[f1378,f101])).

fof(f1378,plain,
    ( r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f1376])).

fof(f1426,plain,(
    spl5_11 ),
    inference(avatar_contradiction_clause,[],[f1425])).

fof(f1425,plain,
    ( $false
    | spl5_11 ),
    inference(subsumption_resolution,[],[f1424,f148])).

fof(f1424,plain,
    ( ~ m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | spl5_11 ),
    inference(subsumption_resolution,[],[f1423,f58])).

fof(f1423,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | spl5_11 ),
    inference(resolution,[],[f1402,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f1402,plain,
    ( ~ r2_hidden(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f1400])).

fof(f1400,plain,
    ( spl5_11
  <=> r2_hidden(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f1408,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f1407])).

fof(f1407,plain,
    ( $false
    | spl5_10 ),
    inference(subsumption_resolution,[],[f1406,f149])).

fof(f1406,plain,
    ( ~ m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | spl5_10 ),
    inference(subsumption_resolution,[],[f1405,f58])).

fof(f1405,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | spl5_10 ),
    inference(resolution,[],[f1398,f97])).

fof(f1398,plain,
    ( ~ r2_hidden(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f1396])).

fof(f1396,plain,
    ( spl5_10
  <=> r2_hidden(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f1403,plain,
    ( ~ spl5_10
    | ~ spl5_11
    | spl5_9 ),
    inference(avatar_split_clause,[],[f1393,f1380,f1400,f1396])).

fof(f1393,plain,
    ( ~ r2_hidden(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | ~ r2_hidden(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | spl5_9 ),
    inference(resolution,[],[f1382,f59])).

fof(f59,plain,(
    ! [X2,X1] :
      ( r2_hidden(k3_xboole_0(X1,X2),sK0)
      | ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1382,plain,
    ( ~ r2_hidden(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f1380])).

fof(f1383,plain,
    ( spl5_8
    | ~ spl5_9
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f1374,f214,f1380,f1376])).

fof(f1374,plain,
    ( ~ r2_hidden(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0)
    | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f1373,f96])).

fof(f1373,plain,
    ( r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ r2_hidden(k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f1372,f96])).

fof(f1372,plain,
    ( r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ r2_hidden(k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f1369,f149])).

fof(f1369,plain,
    ( r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
    | ~ r2_hidden(k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f455,f117])).

fof(f455,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),X0),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
        | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),X0)),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
        | ~ m1_subset_1(X0,sK0)
        | ~ r2_hidden(k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),X0),sK0) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f452,f148])).

fof(f452,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),X0),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
        | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),X0)),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
        | ~ r2_hidden(k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),X0),sK0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f430,f251])).

fof(f430,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),X0),sK0)
        | ~ r1_tarski(k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),X0),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
        | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),X0)),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) )
    | ~ spl5_2 ),
    inference(resolution,[],[f386,f95])).

fof(f386,plain,
    ( ! [X9] :
        ( ~ r1_tarski(X9,sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
        | ~ m1_subset_1(X9,sK0)
        | ~ r1_tarski(X9,sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
        | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),X9),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f385,f105])).

fof(f385,plain,
    ( ! [X9] :
        ( r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),X9),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
        | ~ m1_subset_1(X9,sK0)
        | ~ r1_tarski(X9,sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
        | ~ r1_tarski(X9,sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
        | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f384,f109])).

fof(f384,plain,
    ( ! [X9] :
        ( r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),X9),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
        | ~ m1_subset_1(X9,sK0)
        | ~ r1_tarski(X9,sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
        | ~ r1_tarski(X9,sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
        | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
        | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f383,f104])).

fof(f383,plain,
    ( ! [X9] :
        ( r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),X9),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
        | ~ m1_subset_1(X9,sK0)
        | ~ r1_tarski(X9,sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
        | ~ r1_tarski(X9,sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
        | v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
        | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
        | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f382,f149])).

fof(f382,plain,
    ( ! [X9] :
        ( r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),X9),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
        | ~ m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
        | ~ m1_subset_1(X9,sK0)
        | ~ r1_tarski(X9,sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
        | ~ r1_tarski(X9,sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
        | v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
        | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
        | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f378,f148])).

fof(f378,plain,
    ( ! [X9] :
        ( ~ m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
        | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),X9),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
        | ~ m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)
        | ~ m1_subset_1(X9,sK0)
        | ~ r1_tarski(X9,sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))
        | ~ r1_tarski(X9,sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))
        | v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
        | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
        | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) )
    | ~ spl5_2 ),
    inference(resolution,[],[f370,f88])).

fof(f370,plain,
    ( ! [X2,X0,X1] :
        ( r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(X0,X1))
        | ~ m1_subset_1(X1,sK0)
        | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(X0,X1),X2),X0)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X2,sK0)
        | ~ r1_tarski(X2,X0)
        | ~ r1_tarski(X2,X1) )
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f366])).

fof(f366,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(X0,X1),X2),X0)
        | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(X0,X1))
        | ~ m1_subset_1(X2,sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X2,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ r1_tarski(X2,X0)
        | ~ r1_tarski(X2,X1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f365,f258])).

fof(f365,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r1_lattice3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6)
      | ~ m1_subset_1(X3,X4)
      | ~ m1_subset_1(X5,X4)
      | r1_orders_2(g1_orders_2(X4,k1_yellow_1(X4)),sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X3)
      | r2_yellow_0(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5))
      | ~ m1_subset_1(X6,X4) ) ),
    inference(subsumption_resolution,[],[f188,f172])).

fof(f188,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ m1_subset_1(X6,X4)
      | ~ m1_subset_1(X3,X4)
      | ~ m1_subset_1(X5,X4)
      | ~ m1_subset_1(sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X4)
      | r1_orders_2(g1_orders_2(X4,k1_yellow_1(X4)),sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X3)
      | r2_yellow_0(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5))
      | ~ r1_lattice3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6) ) ),
    inference(forward_demodulation,[],[f187,f135])).

fof(f187,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ m1_subset_1(X3,X4)
      | ~ m1_subset_1(X5,X4)
      | ~ m1_subset_1(sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X4)
      | r1_orders_2(g1_orders_2(X4,k1_yellow_1(X4)),sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X3)
      | r2_yellow_0(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5))
      | ~ r1_lattice3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(g1_orders_2(X4,k1_yellow_1(X4)))) ) ),
    inference(subsumption_resolution,[],[f186,f105])).

fof(f186,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ m1_subset_1(X3,X4)
      | ~ m1_subset_1(X5,X4)
      | ~ m1_subset_1(sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X4)
      | r1_orders_2(g1_orders_2(X4,k1_yellow_1(X4)),sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X3)
      | r2_yellow_0(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5))
      | ~ r1_lattice3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(g1_orders_2(X4,k1_yellow_1(X4))))
      | ~ v5_orders_2(g1_orders_2(X4,k1_yellow_1(X4))) ) ),
    inference(subsumption_resolution,[],[f182,f109])).

fof(f182,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ m1_subset_1(X3,X4)
      | ~ m1_subset_1(X5,X4)
      | ~ m1_subset_1(sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X4)
      | r1_orders_2(g1_orders_2(X4,k1_yellow_1(X4)),sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X3)
      | r2_yellow_0(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5))
      | ~ r1_lattice3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(g1_orders_2(X4,k1_yellow_1(X4))))
      | ~ l1_orders_2(g1_orders_2(X4,k1_yellow_1(X4)))
      | ~ v5_orders_2(g1_orders_2(X4,k1_yellow_1(X4))) ) ),
    inference(resolution,[],[f176,f93])).

fof(f176,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),k2_tarski(X1,X2),X3)
      | ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X3,X0)
      | r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X3,X1) ) ),
    inference(forward_demodulation,[],[f175,f135])).

fof(f175,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),k2_tarski(X1,X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X3,X1) ) ),
    inference(forward_demodulation,[],[f174,f135])).

fof(f174,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,X0)
      | ~ r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),k2_tarski(X1,X2),X3)
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X3,X1) ) ),
    inference(forward_demodulation,[],[f173,f135])).

fof(f173,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),k2_tarski(X1,X2),X3)
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X3,X1) ) ),
    inference(resolution,[],[f79,f109])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f336,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f334,f58])).

fof(f334,plain,
    ( v1_xboole_0(sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f212,f112])).

fof(f112,plain,(
    ! [X0] :
      ( ~ v2_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f73,f61])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(f212,plain,
    ( v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f210])).

fof(f216,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f208,f214,f210])).

fof(f208,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK0)
      | ~ m1_subset_1(X0,sK0)
      | ~ r1_tarski(X1,X0)
      | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0)
      | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f207])).

fof(f207,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK0)
      | ~ m1_subset_1(X0,sK0)
      | ~ r1_tarski(X1,X0)
      | ~ m1_subset_1(X1,sK0)
      | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0)
      | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(forward_demodulation,[],[f206,f135])).

fof(f206,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK0)
      | ~ r1_tarski(X1,X0)
      | ~ m1_subset_1(X1,sK0)
      | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f205])).

fof(f205,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK0)
      | ~ m1_subset_1(X0,sK0)
      | ~ r1_tarski(X1,X0)
      | ~ m1_subset_1(X1,sK0)
      | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(forward_demodulation,[],[f204,f135])).

fof(f204,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK0)
      | ~ r1_tarski(X1,X0)
      | ~ m1_subset_1(X1,sK0)
      | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f203,f107])).

fof(f203,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK0)
      | ~ r1_tarski(X1,X0)
      | ~ m1_subset_1(X1,sK0)
      | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f202,f109])).

fof(f202,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK0)
      | ~ r1_tarski(X1,X0)
      | ~ m1_subset_1(X1,sK0)
      | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(resolution,[],[f201,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f201,plain,(
    ! [X0,X1] :
      ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0)
      | ~ m1_subset_1(X0,sK0)
      | ~ r1_tarski(X1,X0)
      | ~ m1_subset_1(X1,sK0) ) ),
    inference(resolution,[],[f200,f58])).

fof(f200,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0)
      | r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(forward_demodulation,[],[f199,f135])).

fof(f199,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f114,f135])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f77,f61,f61,f61])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:52:08 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.49  % (15163)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.49  % (15163)Refutation not found, incomplete strategy% (15163)------------------------------
% 0.19/0.49  % (15163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (15154)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.49  % (15163)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (15163)Memory used [KB]: 10618
% 0.19/0.49  % (15163)Time elapsed: 0.092 s
% 0.19/0.49  % (15163)------------------------------
% 0.19/0.49  % (15163)------------------------------
% 0.19/0.49  % (15153)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.51  % (15169)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.52  % (15150)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.52  % (15150)Refutation not found, incomplete strategy% (15150)------------------------------
% 0.19/0.52  % (15150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (15150)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (15150)Memory used [KB]: 6268
% 0.19/0.52  % (15150)Time elapsed: 0.125 s
% 0.19/0.52  % (15150)------------------------------
% 0.19/0.52  % (15150)------------------------------
% 0.19/0.52  % (15171)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.52  % (15148)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.52  % (15147)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.52  % (15149)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.52  % (15155)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.52  % (15148)Refutation not found, incomplete strategy% (15148)------------------------------
% 0.19/0.52  % (15148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (15148)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (15148)Memory used [KB]: 10746
% 0.19/0.52  % (15148)Time elapsed: 0.125 s
% 0.19/0.52  % (15148)------------------------------
% 0.19/0.52  % (15148)------------------------------
% 0.19/0.52  % (15161)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.52  % (15156)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.52  % (15155)Refutation not found, incomplete strategy% (15155)------------------------------
% 0.19/0.52  % (15155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (15155)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (15155)Memory used [KB]: 10618
% 0.19/0.52  % (15155)Time elapsed: 0.110 s
% 0.19/0.52  % (15155)------------------------------
% 0.19/0.52  % (15155)------------------------------
% 0.19/0.52  % (15156)Refutation not found, incomplete strategy% (15156)------------------------------
% 0.19/0.52  % (15156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (15156)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (15156)Memory used [KB]: 10618
% 0.19/0.52  % (15156)Time elapsed: 0.124 s
% 0.19/0.52  % (15156)------------------------------
% 0.19/0.52  % (15156)------------------------------
% 0.19/0.52  % (15162)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.53  % (15167)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.36/0.53  % (15165)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.36/0.53  % (15164)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.36/0.53  % (15172)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.53  % (15151)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.36/0.53  % (15146)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.36/0.53  % (15146)Refutation not found, incomplete strategy% (15146)------------------------------
% 1.36/0.53  % (15146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.53  % (15146)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.53  
% 1.36/0.53  % (15146)Memory used [KB]: 1663
% 1.36/0.53  % (15146)Time elapsed: 0.134 s
% 1.36/0.53  % (15146)------------------------------
% 1.36/0.53  % (15146)------------------------------
% 1.36/0.53  % (15175)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.54  % (15157)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.36/0.54  % (15173)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.54  % (15160)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.36/0.54  % (15166)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.36/0.54  % (15159)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.58/0.54  % (15152)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.58/0.55  % (15170)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.58/0.55  % (15174)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.58/0.55  % (15158)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.58/0.56  % (15168)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.58/0.56  % (15157)Refutation not found, incomplete strategy% (15157)------------------------------
% 1.58/0.56  % (15157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.56  % (15157)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.56  
% 1.58/0.56  % (15168)Refutation not found, incomplete strategy% (15168)------------------------------
% 1.58/0.56  % (15168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.56  % (15157)Memory used [KB]: 10618
% 1.58/0.56  % (15168)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.56  % (15157)Time elapsed: 0.148 s
% 1.58/0.56  
% 1.58/0.56  % (15157)------------------------------
% 1.58/0.56  % (15157)------------------------------
% 1.58/0.56  % (15168)Memory used [KB]: 10746
% 1.58/0.56  % (15168)Time elapsed: 0.168 s
% 1.58/0.56  % (15168)------------------------------
% 1.58/0.56  % (15168)------------------------------
% 1.58/0.61  % (15176)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.58/0.61  % (15176)Refutation not found, incomplete strategy% (15176)------------------------------
% 1.58/0.61  % (15176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.61  % (15176)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.61  
% 1.58/0.61  % (15176)Memory used [KB]: 6268
% 1.58/0.61  % (15176)Time elapsed: 0.079 s
% 1.58/0.61  % (15176)------------------------------
% 1.58/0.61  % (15176)------------------------------
% 2.07/0.64  % (15179)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.07/0.65  % (15177)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.07/0.65  % (15180)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.07/0.66  % (15180)Refutation not found, incomplete strategy% (15180)------------------------------
% 2.07/0.66  % (15180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.66  % (15180)Termination reason: Refutation not found, incomplete strategy
% 2.07/0.66  
% 2.07/0.66  % (15180)Memory used [KB]: 10618
% 2.07/0.66  % (15180)Time elapsed: 0.076 s
% 2.07/0.66  % (15180)------------------------------
% 2.07/0.66  % (15180)------------------------------
% 2.07/0.67  % (15183)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.43/0.69  % (15178)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.43/0.70  % (15181)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.43/0.72  % (15147)Refutation not found, incomplete strategy% (15147)------------------------------
% 2.43/0.72  % (15147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.43/0.72  % (15147)Termination reason: Refutation not found, incomplete strategy
% 2.43/0.72  
% 2.43/0.72  % (15147)Memory used [KB]: 6268
% 2.43/0.72  % (15147)Time elapsed: 0.315 s
% 2.43/0.72  % (15147)------------------------------
% 2.43/0.72  % (15147)------------------------------
% 2.43/0.73  % (15184)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.43/0.73  % (15182)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.92/0.77  % (15177)Refutation not found, incomplete strategy% (15177)------------------------------
% 2.92/0.77  % (15177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.92/0.78  % (15177)Termination reason: Refutation not found, incomplete strategy
% 2.92/0.78  
% 2.92/0.78  % (15177)Memory used [KB]: 6268
% 2.92/0.78  % (15177)Time elapsed: 0.220 s
% 2.92/0.78  % (15177)------------------------------
% 2.92/0.78  % (15177)------------------------------
% 2.92/0.80  % (15185)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 3.26/0.81  % (15151)Time limit reached!
% 3.26/0.81  % (15151)------------------------------
% 3.26/0.81  % (15151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.26/0.81  % (15151)Termination reason: Time limit
% 3.26/0.81  % (15151)Termination phase: Saturation
% 3.26/0.81  
% 3.26/0.81  % (15151)Memory used [KB]: 8827
% 3.26/0.81  % (15151)Time elapsed: 0.400 s
% 3.26/0.81  % (15151)------------------------------
% 3.26/0.81  % (15151)------------------------------
% 3.26/0.83  % (15149)Refutation found. Thanks to Tanya!
% 3.26/0.83  % SZS status Theorem for theBenchmark
% 3.45/0.85  % SZS output start Proof for theBenchmark
% 3.45/0.85  fof(f2690,plain,(
% 3.45/0.85    $false),
% 3.45/0.85    inference(avatar_sat_refutation,[],[f216,f336,f1383,f1403,f1408,f1426,f1495,f1515,f1520,f1584,f1597,f1677,f1743,f2689])).
% 3.45/0.85  fof(f2689,plain,(
% 3.45/0.85    spl5_1 | spl5_5 | ~spl5_13 | ~spl5_18 | ~spl5_19 | spl5_29),
% 3.45/0.85    inference(avatar_contradiction_clause,[],[f2688])).
% 3.45/0.85  fof(f2688,plain,(
% 3.45/0.85    $false | (spl5_1 | spl5_5 | ~spl5_13 | ~spl5_18 | ~spl5_19 | spl5_29)),
% 3.45/0.85    inference(subsumption_resolution,[],[f2687,f1477])).
% 3.45/0.85  fof(f1477,plain,(
% 3.45/0.85    m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK0) | ~spl5_13),
% 3.45/0.85    inference(avatar_component_clause,[],[f1476])).
% 3.45/0.85  fof(f1476,plain,(
% 3.45/0.85    spl5_13 <=> m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK0)),
% 3.45/0.85    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 3.45/0.85  fof(f2687,plain,(
% 3.45/0.85    ~m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK0) | (spl5_1 | spl5_5 | ~spl5_13 | ~spl5_18 | ~spl5_19 | spl5_29)),
% 3.45/0.85    inference(subsumption_resolution,[],[f2686,f148])).
% 3.45/0.85  fof(f148,plain,(
% 3.45/0.85    m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)),
% 3.45/0.85    inference(resolution,[],[f143,f104])).
% 3.45/0.85  fof(f104,plain,(
% 3.45/0.85    ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))),
% 3.45/0.85    inference(definition_unfolding,[],[f60,f61])).
% 3.45/0.86  fof(f61,plain,(
% 3.45/0.86    ( ! [X0] : (k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0))) )),
% 3.45/0.86    inference(cnf_transformation,[],[f12])).
% 3.45/0.86  fof(f12,axiom,(
% 3.45/0.86    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0))),
% 3.45/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_yellow_1)).
% 3.45/0.86  fof(f60,plain,(
% 3.45/0.86    ~v2_lattice3(k2_yellow_1(sK0))),
% 3.45/0.86    inference(cnf_transformation,[],[f45])).
% 3.45/0.86  fof(f45,plain,(
% 3.45/0.86    ~v2_lattice3(k2_yellow_1(sK0)) & ! [X1,X2] : (r2_hidden(k3_xboole_0(X1,X2),sK0) | ~r2_hidden(X2,sK0) | ~r2_hidden(X1,sK0)) & ~v1_xboole_0(sK0)),
% 3.45/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f44])).
% 3.45/0.86  fof(f44,plain,(
% 3.45/0.86    ? [X0] : (~v2_lattice3(k2_yellow_1(X0)) & ! [X1,X2] : (r2_hidden(k3_xboole_0(X1,X2),X0) | ~r2_hidden(X2,X0) | ~r2_hidden(X1,X0)) & ~v1_xboole_0(X0)) => (~v2_lattice3(k2_yellow_1(sK0)) & ! [X2,X1] : (r2_hidden(k3_xboole_0(X1,X2),sK0) | ~r2_hidden(X2,sK0) | ~r2_hidden(X1,sK0)) & ~v1_xboole_0(sK0))),
% 3.45/0.86    introduced(choice_axiom,[])).
% 3.45/0.86  fof(f22,plain,(
% 3.45/0.86    ? [X0] : (~v2_lattice3(k2_yellow_1(X0)) & ! [X1,X2] : (r2_hidden(k3_xboole_0(X1,X2),X0) | ~r2_hidden(X2,X0) | ~r2_hidden(X1,X0)) & ~v1_xboole_0(X0))),
% 3.45/0.86    inference(flattening,[],[f21])).
% 3.45/0.86  fof(f21,plain,(
% 3.45/0.86    ? [X0] : ((~v2_lattice3(k2_yellow_1(X0)) & ! [X1,X2] : (r2_hidden(k3_xboole_0(X1,X2),X0) | (~r2_hidden(X2,X0) | ~r2_hidden(X1,X0)))) & ~v1_xboole_0(X0))),
% 3.45/0.86    inference(ennf_transformation,[],[f20])).
% 3.45/0.86  fof(f20,negated_conjecture,(
% 3.45/0.86    ~! [X0] : (~v1_xboole_0(X0) => (! [X1,X2] : ((r2_hidden(X2,X0) & r2_hidden(X1,X0)) => r2_hidden(k3_xboole_0(X1,X2),X0)) => v2_lattice3(k2_yellow_1(X0))))),
% 3.45/0.86    inference(negated_conjecture,[],[f19])).
% 3.45/0.86  fof(f19,conjecture,(
% 3.45/0.86    ! [X0] : (~v1_xboole_0(X0) => (! [X1,X2] : ((r2_hidden(X2,X0) & r2_hidden(X1,X0)) => r2_hidden(k3_xboole_0(X1,X2),X0)) => v2_lattice3(k2_yellow_1(X0))))),
% 3.45/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow_1)).
% 3.45/0.86  fof(f143,plain,(
% 3.45/0.86    ( ! [X2] : (v2_lattice3(g1_orders_2(X2,k1_yellow_1(X2))) | m1_subset_1(sK2(g1_orders_2(X2,k1_yellow_1(X2))),X2)) )),
% 3.45/0.86    inference(subsumption_resolution,[],[f142,f105])).
% 3.45/0.86  fof(f105,plain,(
% 3.45/0.86    ( ! [X0] : (v5_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 3.45/0.86    inference(definition_unfolding,[],[f70,f61])).
% 3.45/0.86  fof(f70,plain,(
% 3.45/0.86    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 3.45/0.86    inference(cnf_transformation,[],[f15])).
% 3.45/0.86  fof(f15,axiom,(
% 3.45/0.86    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.45/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).
% 3.45/0.86  fof(f142,plain,(
% 3.45/0.86    ( ! [X2] : (m1_subset_1(sK2(g1_orders_2(X2,k1_yellow_1(X2))),X2) | v2_lattice3(g1_orders_2(X2,k1_yellow_1(X2))) | ~v5_orders_2(g1_orders_2(X2,k1_yellow_1(X2)))) )),
% 3.45/0.86    inference(subsumption_resolution,[],[f137,f109])).
% 3.45/0.86  fof(f109,plain,(
% 3.45/0.86    ( ! [X0] : (l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 3.45/0.86    inference(definition_unfolding,[],[f72,f61])).
% 3.45/0.86  fof(f72,plain,(
% 3.45/0.86    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 3.45/0.86    inference(cnf_transformation,[],[f14])).
% 3.45/0.86  fof(f14,axiom,(
% 3.45/0.86    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.45/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 3.45/0.86  fof(f137,plain,(
% 3.45/0.86    ( ! [X2] : (m1_subset_1(sK2(g1_orders_2(X2,k1_yellow_1(X2))),X2) | v2_lattice3(g1_orders_2(X2,k1_yellow_1(X2))) | ~l1_orders_2(g1_orders_2(X2,k1_yellow_1(X2))) | ~v5_orders_2(g1_orders_2(X2,k1_yellow_1(X2)))) )),
% 3.45/0.86    inference(superposition,[],[f87,f135])).
% 3.45/0.86  fof(f135,plain,(
% 3.45/0.86    ( ! [X0] : (u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X0) )),
% 3.45/0.86    inference(equality_resolution,[],[f129])).
% 3.45/0.86  fof(f129,plain,(
% 3.45/0.86    ( ! [X0,X1] : (g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,k1_yellow_1(X1)) | u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X1) )),
% 3.45/0.86    inference(subsumption_resolution,[],[f128,f109])).
% 3.45/0.86  fof(f128,plain,(
% 3.45/0.86    ( ! [X0,X1] : (u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X1 | g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,k1_yellow_1(X1)) | ~l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 3.45/0.86    inference(resolution,[],[f126,f108])).
% 3.45/0.86  fof(f108,plain,(
% 3.45/0.86    ( ! [X0] : (v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 3.45/0.86    inference(definition_unfolding,[],[f67,f61])).
% 3.45/0.86  fof(f67,plain,(
% 3.45/0.86    ( ! [X0] : (v1_orders_2(k2_yellow_1(X0))) )),
% 3.45/0.86    inference(cnf_transformation,[],[f15])).
% 3.45/0.86  fof(f126,plain,(
% 3.45/0.86    ( ! [X0,X1] : (~v1_orders_2(X0) | u1_struct_0(X0) = X1 | g1_orders_2(X1,k1_yellow_1(X1)) != X0 | ~l1_orders_2(X0)) )),
% 3.45/0.86    inference(superposition,[],[f125,f78])).
% 3.45/0.86  fof(f78,plain,(
% 3.45/0.86    ( ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0) | ~l1_orders_2(X0)) )),
% 3.45/0.86    inference(cnf_transformation,[],[f28])).
% 3.45/0.86  fof(f28,plain,(
% 3.45/0.86    ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0) | ~l1_orders_2(X0))),
% 3.45/0.86    inference(flattening,[],[f27])).
% 3.45/0.86  fof(f27,plain,(
% 3.45/0.86    ! [X0] : ((g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0)) | ~l1_orders_2(X0))),
% 3.45/0.86    inference(ennf_transformation,[],[f5])).
% 3.45/0.86  fof(f5,axiom,(
% 3.45/0.86    ! [X0] : (l1_orders_2(X0) => (v1_orders_2(X0) => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0))),
% 3.45/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).
% 3.45/0.86  fof(f125,plain,(
% 3.45/0.86    ( ! [X2,X0,X1] : (g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2) | X0 = X1) )),
% 3.45/0.86    inference(resolution,[],[f98,f66])).
% 3.45/0.86  fof(f66,plain,(
% 3.45/0.86    ( ! [X0] : (m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.45/0.86    inference(cnf_transformation,[],[f13])).
% 3.45/0.86  fof(f13,axiom,(
% 3.45/0.86    ! [X0] : (m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k1_yellow_1(X0),X0) & v8_relat_2(k1_yellow_1(X0)) & v4_relat_2(k1_yellow_1(X0)) & v1_relat_2(k1_yellow_1(X0)))),
% 3.45/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_1)).
% 3.45/0.86  fof(f98,plain,(
% 3.45/0.86    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2) )),
% 3.45/0.86    inference(cnf_transformation,[],[f37])).
% 3.45/0.86  fof(f37,plain,(
% 3.45/0.86    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 3.45/0.86    inference(ennf_transformation,[],[f6])).
% 3.45/0.86  fof(f6,axiom,(
% 3.45/0.86    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 3.45/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).
% 3.45/0.86  fof(f87,plain,(
% 3.45/0.86    ( ! [X0] : (m1_subset_1(sK2(X0),u1_struct_0(X0)) | v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 3.45/0.86    inference(cnf_transformation,[],[f51])).
% 3.45/0.86  fof(f51,plain,(
% 3.45/0.86    ! [X0] : (((v2_lattice3(X0) | ((~r2_yellow_0(X0,k2_tarski(sK1(X0),sK2(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))) & m1_subset_1(sK1(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (r2_yellow_0(X0,k2_tarski(X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v2_lattice3(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 3.45/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f48,f50,f49])).
% 3.45/0.86  fof(f49,plain,(
% 3.45/0.86    ! [X0] : (? [X1] : (? [X2] : (~r2_yellow_0(X0,k2_tarski(X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (~r2_yellow_0(X0,k2_tarski(sK1(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK1(X0),u1_struct_0(X0))))),
% 3.45/0.86    introduced(choice_axiom,[])).
% 3.45/0.86  fof(f50,plain,(
% 3.45/0.86    ! [X0] : (? [X2] : (~r2_yellow_0(X0,k2_tarski(sK1(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => (~r2_yellow_0(X0,k2_tarski(sK1(X0),sK2(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 3.45/0.86    introduced(choice_axiom,[])).
% 3.45/0.86  fof(f48,plain,(
% 3.45/0.86    ! [X0] : (((v2_lattice3(X0) | ? [X1] : (? [X2] : (~r2_yellow_0(X0,k2_tarski(X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (r2_yellow_0(X0,k2_tarski(X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v2_lattice3(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 3.45/0.86    inference(rectify,[],[f47])).
% 3.45/0.86  fof(f47,plain,(
% 3.45/0.86    ! [X0] : (((v2_lattice3(X0) | ? [X1] : (? [X2] : (~r2_yellow_0(X0,k2_tarski(X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (r2_yellow_0(X0,k2_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v2_lattice3(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 3.45/0.86    inference(nnf_transformation,[],[f32])).
% 3.45/0.86  fof(f32,plain,(
% 3.45/0.86    ! [X0] : ((v2_lattice3(X0) <=> ! [X1] : (! [X2] : (r2_yellow_0(X0,k2_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 3.45/0.86    inference(flattening,[],[f31])).
% 3.45/0.86  fof(f31,plain,(
% 3.45/0.86    ! [X0] : ((v2_lattice3(X0) <=> ! [X1] : (! [X2] : (r2_yellow_0(X0,k2_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 3.45/0.86    inference(ennf_transformation,[],[f10])).
% 3.45/0.86  fof(f10,axiom,(
% 3.45/0.86    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => (v2_lattice3(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r2_yellow_0(X0,k2_tarski(X1,X2))))))),
% 3.45/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_yellow_0)).
% 3.45/0.86  fof(f2686,plain,(
% 3.45/0.86    ~m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | ~m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK0) | (spl5_1 | spl5_5 | ~spl5_13 | ~spl5_18 | ~spl5_19 | spl5_29)),
% 3.45/0.86    inference(subsumption_resolution,[],[f2684,f1676])).
% 3.45/0.86  fof(f1676,plain,(
% 3.45/0.86    ~r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | spl5_29),
% 3.45/0.86    inference(avatar_component_clause,[],[f1674])).
% 3.45/0.86  fof(f1674,plain,(
% 3.45/0.86    spl5_29 <=> r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),
% 3.45/0.86    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 3.45/0.86  fof(f2684,plain,(
% 3.45/0.86    r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | ~m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK0) | (spl5_1 | spl5_5 | ~spl5_13 | ~spl5_18 | ~spl5_19)),
% 3.45/0.86    inference(resolution,[],[f1968,f229])).
% 3.45/0.86  fof(f229,plain,(
% 3.45/0.86    ( ! [X0,X1] : (~r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) | r1_tarski(X1,X0) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0)) )),
% 3.45/0.86    inference(resolution,[],[f228,f58])).
% 3.45/0.86  fof(f58,plain,(
% 3.45/0.86    ~v1_xboole_0(sK0)),
% 3.45/0.86    inference(cnf_transformation,[],[f45])).
% 3.45/0.86  fof(f228,plain,(
% 3.45/0.86    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X2,X0) | r1_tarski(X1,X2) | ~r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) | ~m1_subset_1(X1,X0)) )),
% 3.45/0.86    inference(forward_demodulation,[],[f227,f135])).
% 3.45/0.86  fof(f227,plain,(
% 3.45/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r1_tarski(X1,X2) | ~r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | v1_xboole_0(X0)) )),
% 3.45/0.86    inference(forward_demodulation,[],[f115,f135])).
% 3.45/0.86  fof(f115,plain,(
% 3.45/0.86    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | v1_xboole_0(X0)) )),
% 3.45/0.86    inference(definition_unfolding,[],[f76,f61,f61,f61])).
% 3.45/0.86  fof(f76,plain,(
% 3.45/0.86    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 3.45/0.86    inference(cnf_transformation,[],[f46])).
% 3.45/0.86  fof(f46,plain,(
% 3.45/0.86    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 3.45/0.86    inference(nnf_transformation,[],[f26])).
% 3.45/0.86  fof(f26,plain,(
% 3.45/0.86    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 3.45/0.86    inference(ennf_transformation,[],[f17])).
% 3.45/0.86  fof(f17,axiom,(
% 3.45/0.86    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 3.45/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).
% 3.45/0.86  fof(f1968,plain,(
% 3.45/0.86    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | (spl5_1 | spl5_5 | ~spl5_13 | ~spl5_18 | ~spl5_19)),
% 3.45/0.86    inference(subsumption_resolution,[],[f1967,f1477])).
% 3.45/0.86  fof(f1967,plain,(
% 3.45/0.86    ~m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK0) | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | (spl5_1 | spl5_5 | ~spl5_18 | ~spl5_19)),
% 3.45/0.86    inference(forward_demodulation,[],[f1966,f135])).
% 3.45/0.86  fof(f1966,plain,(
% 3.45/0.86    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | (spl5_1 | spl5_5 | ~spl5_18 | ~spl5_19)),
% 3.45/0.86    inference(subsumption_resolution,[],[f1965,f148])).
% 3.45/0.86  fof(f1965,plain,(
% 3.45/0.86    ~m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | (spl5_1 | spl5_5 | ~spl5_18 | ~spl5_19)),
% 3.45/0.86    inference(forward_demodulation,[],[f1964,f135])).
% 3.45/0.86  fof(f1964,plain,(
% 3.45/0.86    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | (spl5_1 | spl5_5 | ~spl5_18 | ~spl5_19)),
% 3.45/0.86    inference(subsumption_resolution,[],[f1963,f211])).
% 3.45/0.86  fof(f211,plain,(
% 3.45/0.86    ~v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | spl5_1),
% 3.45/0.86    inference(avatar_component_clause,[],[f210])).
% 3.45/0.86  fof(f210,plain,(
% 3.45/0.86    spl5_1 <=> v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))),
% 3.45/0.86    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 3.45/0.86  fof(f1963,plain,(
% 3.45/0.86    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | (spl5_5 | ~spl5_18 | ~spl5_19)),
% 3.45/0.86    inference(subsumption_resolution,[],[f1962,f107])).
% 3.45/0.86  fof(f107,plain,(
% 3.45/0.86    ( ! [X0] : (v3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 3.45/0.86    inference(definition_unfolding,[],[f68,f61])).
% 3.45/0.86  fof(f68,plain,(
% 3.45/0.86    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 3.45/0.86    inference(cnf_transformation,[],[f15])).
% 3.45/0.86  fof(f1962,plain,(
% 3.45/0.86    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | (spl5_5 | ~spl5_18 | ~spl5_19)),
% 3.45/0.86    inference(subsumption_resolution,[],[f1955,f109])).
% 3.45/0.86  fof(f1955,plain,(
% 3.45/0.86    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | (spl5_5 | ~spl5_18 | ~spl5_19)),
% 3.45/0.86    inference(resolution,[],[f1644,f101])).
% 3.45/0.86  fof(f101,plain,(
% 3.45/0.86    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.45/0.86    inference(cnf_transformation,[],[f57])).
% 3.45/0.86  fof(f57,plain,(
% 3.45/0.86    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.45/0.86    inference(nnf_transformation,[],[f39])).
% 3.45/0.86  fof(f39,plain,(
% 3.45/0.86    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.45/0.86    inference(flattening,[],[f38])).
% 3.45/0.86  fof(f38,plain,(
% 3.45/0.86    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.45/0.86    inference(ennf_transformation,[],[f7])).
% 3.45/0.86  fof(f7,axiom,(
% 3.45/0.86    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 3.45/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 3.45/0.86  fof(f1644,plain,(
% 3.45/0.86    r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | (spl5_5 | ~spl5_18 | ~spl5_19)),
% 3.45/0.86    inference(subsumption_resolution,[],[f1643,f1509])).
% 3.45/0.86  fof(f1509,plain,(
% 3.45/0.86    m1_subset_1(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0) | ~spl5_18),
% 3.45/0.86    inference(avatar_component_clause,[],[f1508])).
% 3.45/0.86  fof(f1508,plain,(
% 3.45/0.86    spl5_18 <=> m1_subset_1(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0)),
% 3.45/0.86    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 3.45/0.86  fof(f1643,plain,(
% 3.45/0.86    r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0) | (spl5_5 | ~spl5_19)),
% 3.45/0.86    inference(subsumption_resolution,[],[f1642,f701])).
% 3.45/0.86  fof(f701,plain,(
% 3.45/0.86    ~r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))) | spl5_5),
% 3.45/0.86    inference(avatar_component_clause,[],[f700])).
% 3.45/0.86  fof(f700,plain,(
% 3.45/0.86    spl5_5 <=> r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))))),
% 3.45/0.86    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 3.45/0.86  fof(f1642,plain,(
% 3.45/0.86    r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))) | ~m1_subset_1(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0) | ~spl5_19),
% 3.45/0.86    inference(subsumption_resolution,[],[f1641,f148])).
% 3.45/0.86  fof(f1641,plain,(
% 3.45/0.86    ~m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))) | ~m1_subset_1(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0) | ~spl5_19),
% 3.45/0.86    inference(subsumption_resolution,[],[f1624,f149])).
% 3.45/0.86  fof(f149,plain,(
% 3.45/0.86    m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)),
% 3.45/0.86    inference(resolution,[],[f145,f104])).
% 3.45/0.86  fof(f145,plain,(
% 3.45/0.86    ( ! [X3] : (v2_lattice3(g1_orders_2(X3,k1_yellow_1(X3))) | m1_subset_1(sK1(g1_orders_2(X3,k1_yellow_1(X3))),X3)) )),
% 3.45/0.86    inference(subsumption_resolution,[],[f144,f105])).
% 3.45/0.86  fof(f144,plain,(
% 3.45/0.86    ( ! [X3] : (m1_subset_1(sK1(g1_orders_2(X3,k1_yellow_1(X3))),X3) | v2_lattice3(g1_orders_2(X3,k1_yellow_1(X3))) | ~v5_orders_2(g1_orders_2(X3,k1_yellow_1(X3)))) )),
% 3.45/0.86    inference(subsumption_resolution,[],[f138,f109])).
% 3.45/0.86  fof(f138,plain,(
% 3.45/0.86    ( ! [X3] : (m1_subset_1(sK1(g1_orders_2(X3,k1_yellow_1(X3))),X3) | v2_lattice3(g1_orders_2(X3,k1_yellow_1(X3))) | ~l1_orders_2(g1_orders_2(X3,k1_yellow_1(X3))) | ~v5_orders_2(g1_orders_2(X3,k1_yellow_1(X3)))) )),
% 3.45/0.86    inference(superposition,[],[f86,f135])).
% 3.45/0.86  fof(f86,plain,(
% 3.45/0.86    ( ! [X0] : (m1_subset_1(sK1(X0),u1_struct_0(X0)) | v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 3.45/0.86    inference(cnf_transformation,[],[f51])).
% 3.45/0.86  fof(f1624,plain,(
% 3.45/0.86    ~m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | ~m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))) | ~m1_subset_1(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0) | ~spl5_19),
% 3.45/0.86    inference(resolution,[],[f1513,f524])).
% 3.45/0.86  fof(f524,plain,(
% 3.45/0.86    ( ! [X6,X4,X5,X3] : (~r1_lattice3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6) | ~m1_subset_1(X3,X4) | ~m1_subset_1(X5,X4) | r1_orders_2(g1_orders_2(X4,k1_yellow_1(X4)),sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X5) | r2_yellow_0(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5)) | ~m1_subset_1(X6,X4)) )),
% 3.45/0.86    inference(subsumption_resolution,[],[f196,f172])).
% 3.45/0.86  fof(f172,plain,(
% 3.45/0.86    ( ! [X2,X0,X1] : (m1_subset_1(sK3(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2),X0) | r2_yellow_0(g1_orders_2(X0,k1_yellow_1(X0)),X1) | ~r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) | ~m1_subset_1(X2,X0)) )),
% 3.45/0.86    inference(subsumption_resolution,[],[f171,f105])).
% 3.45/0.86  fof(f171,plain,(
% 3.45/0.86    ( ! [X2,X0,X1] : (m1_subset_1(sK3(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2),X0) | r2_yellow_0(g1_orders_2(X0,k1_yellow_1(X0)),X1) | ~r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) | ~m1_subset_1(X2,X0) | ~v5_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 3.45/0.86    inference(subsumption_resolution,[],[f170,f109])).
% 3.45/0.86  fof(f170,plain,(
% 3.45/0.86    ( ! [X2,X0,X1] : (m1_subset_1(sK3(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2),X0) | r2_yellow_0(g1_orders_2(X0,k1_yellow_1(X0)),X1) | ~r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) | ~m1_subset_1(X2,X0) | ~l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) | ~v5_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 3.45/0.86    inference(superposition,[],[f92,f135])).
% 3.45/0.86  fof(f92,plain,(
% 3.45/0.86    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r2_yellow_0(X0,X1) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 3.45/0.86    inference(cnf_transformation,[],[f56])).
% 3.45/0.86  fof(f56,plain,(
% 3.45/0.86    ! [X0] : (! [X1] : ((r2_yellow_0(X0,X1) | ! [X2] : ((~r1_orders_2(X0,sK3(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)))) & ((! [X5] : (r1_orders_2(X0,X5,sK4(X0,X1)) | ~r1_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_lattice3(X0,X1,sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))) | ~r2_yellow_0(X0,X1))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 3.45/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f53,f55,f54])).
% 3.45/0.86  fof(f54,plain,(
% 3.45/0.86    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK3(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 3.45/0.86    introduced(choice_axiom,[])).
% 3.45/0.86  fof(f55,plain,(
% 3.45/0.86    ! [X1,X0] : (? [X4] : (! [X5] : (r1_orders_2(X0,X5,X4) | ~r1_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_lattice3(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (! [X5] : (r1_orders_2(X0,X5,sK4(X0,X1)) | ~r1_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_lattice3(X0,X1,sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 3.45/0.86    introduced(choice_axiom,[])).
% 3.45/0.86  fof(f53,plain,(
% 3.45/0.86    ! [X0] : (! [X1] : ((r2_yellow_0(X0,X1) | ! [X2] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (? [X4] : (! [X5] : (r1_orders_2(X0,X5,X4) | ~r1_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_lattice3(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_yellow_0(X0,X1))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 3.45/0.86    inference(rectify,[],[f52])).
% 3.45/0.86  fof(f52,plain,(
% 3.45/0.86    ! [X0] : (! [X1] : ((r2_yellow_0(X0,X1) | ! [X2] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (? [X2] : (! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_yellow_0(X0,X1))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 3.45/0.86    inference(nnf_transformation,[],[f34])).
% 3.45/0.86  fof(f34,plain,(
% 3.45/0.86    ! [X0] : (! [X1] : (r2_yellow_0(X0,X1) <=> ? [X2] : (! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 3.45/0.86    inference(flattening,[],[f33])).
% 3.45/0.86  fof(f33,plain,(
% 3.45/0.86    ! [X0] : (! [X1] : (r2_yellow_0(X0,X1) <=> ? [X2] : (! [X3] : ((r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 3.45/0.86    inference(ennf_transformation,[],[f9])).
% 3.45/0.86  fof(f9,axiom,(
% 3.45/0.86    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (r2_yellow_0(X0,X1) <=> ? [X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) => r1_orders_2(X0,X3,X2))) & r1_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 3.45/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow_0)).
% 3.45/0.86  fof(f196,plain,(
% 3.45/0.86    ( ! [X6,X4,X5,X3] : (~m1_subset_1(X6,X4) | ~m1_subset_1(X3,X4) | ~m1_subset_1(X5,X4) | ~m1_subset_1(sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X4) | r1_orders_2(g1_orders_2(X4,k1_yellow_1(X4)),sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X5) | r2_yellow_0(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5)) | ~r1_lattice3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6)) )),
% 3.45/0.86    inference(forward_demodulation,[],[f195,f135])).
% 3.45/0.86  fof(f195,plain,(
% 3.45/0.86    ( ! [X6,X4,X5,X3] : (~m1_subset_1(X3,X4) | ~m1_subset_1(X5,X4) | ~m1_subset_1(sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X4) | r1_orders_2(g1_orders_2(X4,k1_yellow_1(X4)),sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X5) | r2_yellow_0(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5)) | ~r1_lattice3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6) | ~m1_subset_1(X6,u1_struct_0(g1_orders_2(X4,k1_yellow_1(X4))))) )),
% 3.45/0.86    inference(subsumption_resolution,[],[f194,f105])).
% 3.45/0.86  fof(f194,plain,(
% 3.45/0.86    ( ! [X6,X4,X5,X3] : (~m1_subset_1(X3,X4) | ~m1_subset_1(X5,X4) | ~m1_subset_1(sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X4) | r1_orders_2(g1_orders_2(X4,k1_yellow_1(X4)),sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X5) | r2_yellow_0(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5)) | ~r1_lattice3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6) | ~m1_subset_1(X6,u1_struct_0(g1_orders_2(X4,k1_yellow_1(X4)))) | ~v5_orders_2(g1_orders_2(X4,k1_yellow_1(X4)))) )),
% 3.45/0.86    inference(subsumption_resolution,[],[f190,f109])).
% 3.45/0.86  fof(f190,plain,(
% 3.45/0.86    ( ! [X6,X4,X5,X3] : (~m1_subset_1(X3,X4) | ~m1_subset_1(X5,X4) | ~m1_subset_1(sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X4) | r1_orders_2(g1_orders_2(X4,k1_yellow_1(X4)),sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X5) | r2_yellow_0(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5)) | ~r1_lattice3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6) | ~m1_subset_1(X6,u1_struct_0(g1_orders_2(X4,k1_yellow_1(X4)))) | ~l1_orders_2(g1_orders_2(X4,k1_yellow_1(X4))) | ~v5_orders_2(g1_orders_2(X4,k1_yellow_1(X4)))) )),
% 3.45/0.86    inference(resolution,[],[f180,f93])).
% 3.45/0.86  fof(f93,plain,(
% 3.45/0.86    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,sK3(X0,X1,X2)) | r2_yellow_0(X0,X1) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 3.45/0.86    inference(cnf_transformation,[],[f56])).
% 3.45/0.86  fof(f180,plain,(
% 3.45/0.86    ( ! [X2,X0,X3,X1] : (~r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),k2_tarski(X1,X2),X3) | ~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X3,X0) | r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X3,X2)) )),
% 3.45/0.86    inference(forward_demodulation,[],[f179,f135])).
% 3.45/0.86  fof(f179,plain,(
% 3.45/0.86    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | ~r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),k2_tarski(X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X3,X2)) )),
% 3.45/0.86    inference(forward_demodulation,[],[f178,f135])).
% 3.45/0.86  fof(f178,plain,(
% 3.45/0.86    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,X0) | ~r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),k2_tarski(X1,X2),X3) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | ~m1_subset_1(X3,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X3,X2)) )),
% 3.45/0.86    inference(forward_demodulation,[],[f177,f135])).
% 3.45/0.86  fof(f177,plain,(
% 3.45/0.86    ( ! [X2,X0,X3,X1] : (~r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),k2_tarski(X1,X2),X3) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | ~m1_subset_1(X3,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X3,X2)) )),
% 3.45/0.86    inference(resolution,[],[f80,f109])).
% 3.45/0.86  fof(f80,plain,(
% 3.45/0.86    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~r1_lattice3(X0,k2_tarski(X2,X3),X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X3)) )),
% 3.45/0.86    inference(cnf_transformation,[],[f30])).
% 3.45/0.86  fof(f30,plain,(
% 3.45/0.86    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_lattice3(X0,k2_tarski(X2,X3),X1) | ~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X2,X1)) & ((r1_orders_2(X0,X3,X1) & r1_orders_2(X0,X2,X1)) | ~r2_lattice3(X0,k2_tarski(X2,X3),X1)) & (r1_lattice3(X0,k2_tarski(X2,X3),X1) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2)) & ((r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X1,X2)) | ~r1_lattice3(X0,k2_tarski(X2,X3),X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.45/0.86    inference(flattening,[],[f29])).
% 3.45/0.86  fof(f29,plain,(
% 3.45/0.86    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_lattice3(X0,k2_tarski(X2,X3),X1) | (~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X2,X1))) & ((r1_orders_2(X0,X3,X1) & r1_orders_2(X0,X2,X1)) | ~r2_lattice3(X0,k2_tarski(X2,X3),X1)) & (r1_lattice3(X0,k2_tarski(X2,X3),X1) | (~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2))) & ((r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X1,X2)) | ~r1_lattice3(X0,k2_tarski(X2,X3),X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.45/0.86    inference(ennf_transformation,[],[f11])).
% 3.45/0.86  fof(f11,axiom,(
% 3.45/0.86    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((r1_orders_2(X0,X3,X1) & r1_orders_2(X0,X2,X1)) => r2_lattice3(X0,k2_tarski(X2,X3),X1)) & (r2_lattice3(X0,k2_tarski(X2,X3),X1) => (r1_orders_2(X0,X3,X1) & r1_orders_2(X0,X2,X1))) & ((r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X1,X2)) => r1_lattice3(X0,k2_tarski(X2,X3),X1)) & (r1_lattice3(X0,k2_tarski(X2,X3),X1) => (r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X1,X2))))))))),
% 3.45/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_yellow_0)).
% 3.45/0.86  fof(f1513,plain,(
% 3.45/0.86    r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))) | ~spl5_19),
% 3.45/0.86    inference(avatar_component_clause,[],[f1512])).
% 3.45/0.86  fof(f1512,plain,(
% 3.45/0.86    spl5_19 <=> r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))))),
% 3.45/0.86    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 3.45/0.86  fof(f1743,plain,(
% 3.45/0.86    ~spl5_13 | ~spl5_15 | spl5_28),
% 3.45/0.86    inference(avatar_contradiction_clause,[],[f1742])).
% 3.45/0.86  fof(f1742,plain,(
% 3.45/0.86    $false | (~spl5_13 | ~spl5_15 | spl5_28)),
% 3.45/0.86    inference(subsumption_resolution,[],[f1741,f1477])).
% 3.45/0.86  fof(f1741,plain,(
% 3.45/0.86    ~m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK0) | (~spl5_15 | spl5_28)),
% 3.45/0.86    inference(subsumption_resolution,[],[f1740,f149])).
% 3.45/0.86  fof(f1740,plain,(
% 3.45/0.86    ~m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | ~m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK0) | (~spl5_15 | spl5_28)),
% 3.45/0.86    inference(subsumption_resolution,[],[f1738,f1672])).
% 3.45/0.86  fof(f1672,plain,(
% 3.45/0.86    ~r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | spl5_28),
% 3.45/0.86    inference(avatar_component_clause,[],[f1670])).
% 3.45/0.86  fof(f1670,plain,(
% 3.45/0.86    spl5_28 <=> r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))),
% 3.45/0.86    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 3.45/0.86  fof(f1738,plain,(
% 3.45/0.86    r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | ~m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK0) | ~spl5_15),
% 3.45/0.86    inference(resolution,[],[f1494,f229])).
% 3.45/0.86  fof(f1494,plain,(
% 3.45/0.86    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~spl5_15),
% 3.45/0.86    inference(avatar_component_clause,[],[f1492])).
% 3.45/0.86  fof(f1492,plain,(
% 3.45/0.86    spl5_15 <=> r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))),
% 3.45/0.86    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 3.45/0.86  fof(f1677,plain,(
% 3.45/0.86    ~spl5_28 | ~spl5_29 | ~spl5_2 | spl5_5 | ~spl5_9 | ~spl5_19),
% 3.45/0.86    inference(avatar_split_clause,[],[f1668,f1512,f1380,f700,f214,f1674,f1670])).
% 3.45/0.86  fof(f214,plain,(
% 3.45/0.86    spl5_2 <=> ! [X1,X0] : (~m1_subset_1(X1,sK0) | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) | ~r1_tarski(X1,X0) | ~m1_subset_1(X0,sK0))),
% 3.45/0.86    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 3.45/0.86  fof(f1380,plain,(
% 3.45/0.86    spl5_9 <=> r2_hidden(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0)),
% 3.45/0.86    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 3.45/0.86  fof(f1668,plain,(
% 3.45/0.86    ~r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | (~spl5_2 | spl5_5 | ~spl5_9 | ~spl5_19)),
% 3.45/0.86    inference(subsumption_resolution,[],[f1667,f148])).
% 3.45/0.87  fof(f1667,plain,(
% 3.45/0.87    ~m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | ~r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | (~spl5_2 | spl5_5 | ~spl5_9 | ~spl5_19)),
% 3.45/0.87    inference(subsumption_resolution,[],[f1666,f701])).
% 3.45/0.87  fof(f1666,plain,(
% 3.45/0.87    r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))) | ~m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | ~r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | (~spl5_2 | ~spl5_9 | ~spl5_19)),
% 3.45/0.87    inference(subsumption_resolution,[],[f1665,f1381])).
% 3.45/0.87  fof(f1381,plain,(
% 3.45/0.87    r2_hidden(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0) | ~spl5_9),
% 3.45/0.87    inference(avatar_component_clause,[],[f1380])).
% 3.45/0.87  fof(f1665,plain,(
% 3.45/0.87    ~r2_hidden(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0) | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))) | ~m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | ~r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | (~spl5_2 | ~spl5_19)),
% 3.45/0.87    inference(subsumption_resolution,[],[f1630,f149])).
% 3.45/0.87  fof(f1630,plain,(
% 3.45/0.87    ~m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | ~r2_hidden(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0) | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))) | ~m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | ~r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | (~spl5_2 | ~spl5_19)),
% 3.45/0.87    inference(resolution,[],[f1513,f252])).
% 3.45/0.87  fof(f252,plain,(
% 3.45/0.87    ( ! [X2,X0,X1] : (~r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,k3_xboole_0(X1,X0)) | ~m1_subset_1(X1,sK0) | ~r2_hidden(k3_xboole_0(X1,X0),sK0) | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),X2) | ~m1_subset_1(X0,sK0) | ~r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,k3_xboole_0(X1,X0)),X0) | ~r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,k3_xboole_0(X1,X0)),X1)) ) | ~spl5_2),
% 3.45/0.87    inference(resolution,[],[f251,f224])).
% 3.45/0.87  fof(f224,plain,(
% 3.45/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(k3_xboole_0(X0,X1),sK0) | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),X2) | ~r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,k3_xboole_0(X0,X1)) | ~r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,k3_xboole_0(X0,X1)),X1) | ~r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,k3_xboole_0(X0,X1)),X0)) ) | ~spl5_2),
% 3.45/0.87    inference(resolution,[],[f223,f103])).
% 3.45/0.87  fof(f103,plain,(
% 3.45/0.87    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.45/0.87    inference(cnf_transformation,[],[f43])).
% 3.45/0.87  fof(f43,plain,(
% 3.45/0.87    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.45/0.87    inference(flattening,[],[f42])).
% 3.45/0.87  fof(f42,plain,(
% 3.45/0.87    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.45/0.87    inference(ennf_transformation,[],[f3])).
% 3.45/0.87  fof(f3,axiom,(
% 3.45/0.87    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.45/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 3.45/0.87  fof(f223,plain,(
% 3.45/0.87    ( ! [X0,X1] : (~r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),X1) | ~m1_subset_1(X1,sK0) | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),X0) | ~r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)) ) | ~spl5_2),
% 3.45/0.87    inference(duplicate_literal_removal,[],[f222])).
% 3.45/0.87  fof(f222,plain,(
% 3.45/0.87    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | ~r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),X1) | ~m1_subset_1(X1,sK0) | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),X0) | ~r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1)) ) | ~spl5_2),
% 3.45/0.87    inference(forward_demodulation,[],[f221,f135])).
% 3.45/0.87  fof(f221,plain,(
% 3.45/0.87    ( ! [X0,X1] : (~r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),X1) | ~m1_subset_1(X1,sK0) | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),X0) | ~r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))) ) | ~spl5_2),
% 3.45/0.87    inference(subsumption_resolution,[],[f220,f172])).
% 3.45/0.87  fof(f220,plain,(
% 3.45/0.87    ( ! [X0,X1] : (~m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),sK0) | ~r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),X1) | ~m1_subset_1(X1,sK0) | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),X0) | ~r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))) ) | ~spl5_2),
% 3.45/0.87    inference(subsumption_resolution,[],[f219,f105])).
% 3.45/0.87  fof(f219,plain,(
% 3.45/0.87    ( ! [X0,X1] : (~m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),sK0) | ~r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),X1) | ~m1_subset_1(X1,sK0) | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),X0) | ~r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) ) | ~spl5_2),
% 3.45/0.87    inference(subsumption_resolution,[],[f217,f109])).
% 3.45/0.87  fof(f217,plain,(
% 3.45/0.87    ( ! [X0,X1] : (~m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),sK0) | ~r1_tarski(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1),X1) | ~m1_subset_1(X1,sK0) | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),X0) | ~r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,X1) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) ) | ~spl5_2),
% 3.45/0.87    inference(resolution,[],[f215,f94])).
% 3.45/0.87  fof(f94,plain,(
% 3.45/0.87    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK3(X0,X1,X2),X2) | r2_yellow_0(X0,X1) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 3.45/0.87    inference(cnf_transformation,[],[f56])).
% 3.45/0.87  fof(f215,plain,(
% 3.45/0.87    ( ! [X0,X1] : (r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) | ~m1_subset_1(X1,sK0) | ~r1_tarski(X1,X0) | ~m1_subset_1(X0,sK0)) ) | ~spl5_2),
% 3.45/0.87    inference(avatar_component_clause,[],[f214])).
% 3.45/0.87  fof(f251,plain,(
% 3.45/0.87    ( ! [X2,X3] : (m1_subset_1(k3_xboole_0(X2,X3),sK0) | ~m1_subset_1(X3,sK0) | ~m1_subset_1(X2,sK0) | ~r2_hidden(k3_xboole_0(X2,X3),sK0)) )),
% 3.45/0.87    inference(duplicate_literal_removal,[],[f250])).
% 3.45/0.87  fof(f250,plain,(
% 3.45/0.87    ( ! [X2,X3] : (~m1_subset_1(X2,sK0) | ~m1_subset_1(X3,sK0) | m1_subset_1(k3_xboole_0(X2,X3),sK0) | ~r2_hidden(k3_xboole_0(X2,X3),sK0) | ~m1_subset_1(X2,sK0)) )),
% 3.45/0.87    inference(forward_demodulation,[],[f249,f135])).
% 3.45/0.87  fof(f249,plain,(
% 3.45/0.87    ( ! [X2,X3] : (~m1_subset_1(X3,sK0) | m1_subset_1(k3_xboole_0(X2,X3),sK0) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~r2_hidden(k3_xboole_0(X2,X3),sK0) | ~m1_subset_1(X2,sK0)) )),
% 3.45/0.87    inference(duplicate_literal_removal,[],[f248])).
% 3.45/0.87  fof(f248,plain,(
% 3.45/0.87    ( ! [X2,X3] : (~m1_subset_1(X3,sK0) | m1_subset_1(k3_xboole_0(X2,X3),sK0) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X3,sK0) | ~r2_hidden(k3_xboole_0(X2,X3),sK0) | ~m1_subset_1(X2,sK0)) )),
% 3.45/0.87    inference(forward_demodulation,[],[f247,f135])).
% 3.45/0.87  fof(f247,plain,(
% 3.45/0.87    ( ! [X2,X3] : (m1_subset_1(k3_xboole_0(X2,X3),sK0) | ~m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X3,sK0) | ~r2_hidden(k3_xboole_0(X2,X3),sK0) | ~m1_subset_1(X2,sK0)) )),
% 3.45/0.87    inference(forward_demodulation,[],[f246,f135])).
% 3.45/0.87  fof(f246,plain,(
% 3.45/0.87    ( ! [X2,X3] : (m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X3,sK0) | ~r2_hidden(k3_xboole_0(X2,X3),sK0) | ~m1_subset_1(X2,sK0)) )),
% 3.45/0.87    inference(subsumption_resolution,[],[f244,f109])).
% 3.45/0.87  fof(f244,plain,(
% 3.45/0.87    ( ! [X2,X3] : (m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~m1_subset_1(X3,sK0) | ~r2_hidden(k3_xboole_0(X2,X3),sK0) | ~m1_subset_1(X2,sK0)) )),
% 3.45/0.87    inference(superposition,[],[f102,f242])).
% 3.45/0.87  fof(f242,plain,(
% 3.45/0.87    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) | ~m1_subset_1(X0,sK0) | ~r2_hidden(k3_xboole_0(X1,X0),sK0) | ~m1_subset_1(X1,sK0)) )),
% 3.45/0.87    inference(resolution,[],[f241,f58])).
% 3.45/0.87  fof(f241,plain,(
% 3.45/0.87    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X2,X0) | k3_xboole_0(X1,X2) = k11_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X1,X0)) )),
% 3.45/0.87    inference(forward_demodulation,[],[f240,f135])).
% 3.45/0.87  fof(f240,plain,(
% 3.45/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | k3_xboole_0(X1,X2) = k11_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | v1_xboole_0(X0)) )),
% 3.45/0.87    inference(forward_demodulation,[],[f113,f135])).
% 3.45/0.87  fof(f113,plain,(
% 3.45/0.87    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k11_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | v1_xboole_0(X0)) )),
% 3.45/0.87    inference(definition_unfolding,[],[f75,f61,f61,f61])).
% 3.45/0.87  fof(f75,plain,(
% 3.45/0.87    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 3.45/0.87    inference(cnf_transformation,[],[f25])).
% 3.45/0.87  fof(f25,plain,(
% 3.45/0.87    ! [X0] : (! [X1] : (! [X2] : (k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 3.45/0.87    inference(flattening,[],[f24])).
% 3.45/0.87  fof(f24,plain,(
% 3.45/0.87    ! [X0] : (! [X1] : (! [X2] : ((k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 3.45/0.87    inference(ennf_transformation,[],[f18])).
% 3.45/0.87  fof(f18,axiom,(
% 3.45/0.87    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r2_hidden(k3_xboole_0(X1,X2),X0) => k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)))))),
% 3.45/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_1)).
% 3.45/0.87  fof(f102,plain,(
% 3.45/0.87    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.45/0.87    inference(cnf_transformation,[],[f41])).
% 3.45/0.87  fof(f41,plain,(
% 3.45/0.87    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.45/0.87    inference(flattening,[],[f40])).
% 3.45/0.87  fof(f40,plain,(
% 3.45/0.87    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 3.45/0.87    inference(ennf_transformation,[],[f8])).
% 3.45/0.87  fof(f8,axiom,(
% 3.45/0.87    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 3.45/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).
% 3.45/0.87  fof(f1597,plain,(
% 3.45/0.87    ~spl5_5),
% 3.45/0.87    inference(avatar_contradiction_clause,[],[f1596])).
% 3.45/0.87  fof(f1596,plain,(
% 3.45/0.87    $false | ~spl5_5),
% 3.45/0.87    inference(subsumption_resolution,[],[f1595,f105])).
% 3.45/0.87  fof(f1595,plain,(
% 3.45/0.87    ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl5_5),
% 3.45/0.87    inference(subsumption_resolution,[],[f1594,f109])).
% 3.45/0.87  fof(f1594,plain,(
% 3.45/0.87    ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl5_5),
% 3.45/0.87    inference(subsumption_resolution,[],[f1588,f104])).
% 3.45/0.87  fof(f1588,plain,(
% 3.45/0.87    v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl5_5),
% 3.45/0.87    inference(resolution,[],[f702,f88])).
% 3.45/0.87  fof(f88,plain,(
% 3.45/0.87    ( ! [X0] : (~r2_yellow_0(X0,k2_tarski(sK1(X0),sK2(X0))) | v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 3.45/0.87    inference(cnf_transformation,[],[f51])).
% 3.45/0.87  fof(f702,plain,(
% 3.45/0.87    r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))) | ~spl5_5),
% 3.45/0.87    inference(avatar_component_clause,[],[f700])).
% 3.45/0.87  fof(f1584,plain,(
% 3.45/0.87    ~spl5_2 | ~spl5_18 | spl5_19),
% 3.45/0.87    inference(avatar_contradiction_clause,[],[f1583])).
% 3.45/0.87  fof(f1583,plain,(
% 3.45/0.87    $false | (~spl5_2 | ~spl5_18 | spl5_19)),
% 3.45/0.87    inference(subsumption_resolution,[],[f1582,f117])).
% 3.45/0.87  fof(f117,plain,(
% 3.45/0.87    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 3.45/0.87    inference(superposition,[],[f95,f96])).
% 3.45/0.87  fof(f96,plain,(
% 3.45/0.87    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.45/0.87    inference(cnf_transformation,[],[f1])).
% 3.45/0.87  fof(f1,axiom,(
% 3.45/0.87    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.45/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.45/0.87  fof(f95,plain,(
% 3.45/0.87    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.45/0.87    inference(cnf_transformation,[],[f2])).
% 3.45/0.87  fof(f2,axiom,(
% 3.45/0.87    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.45/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 3.45/0.87  fof(f1582,plain,(
% 3.45/0.87    ~r1_tarski(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | (~spl5_2 | ~spl5_18 | spl5_19)),
% 3.45/0.87    inference(subsumption_resolution,[],[f1581,f95])).
% 3.45/0.87  fof(f1581,plain,(
% 3.45/0.87    ~r1_tarski(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~r1_tarski(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | (~spl5_2 | ~spl5_18 | spl5_19)),
% 3.45/0.87    inference(subsumption_resolution,[],[f1580,f148])).
% 3.45/0.87  fof(f1580,plain,(
% 3.45/0.87    ~m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | ~r1_tarski(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~r1_tarski(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | (~spl5_2 | ~spl5_18 | spl5_19)),
% 3.45/0.87    inference(subsumption_resolution,[],[f1579,f1509])).
% 3.45/0.87  fof(f1579,plain,(
% 3.45/0.87    ~m1_subset_1(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0) | ~m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | ~r1_tarski(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~r1_tarski(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | (~spl5_2 | spl5_19)),
% 3.45/0.87    inference(subsumption_resolution,[],[f1578,f149])).
% 3.45/0.87  fof(f1578,plain,(
% 3.45/0.87    ~m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | ~m1_subset_1(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0) | ~m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | ~r1_tarski(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~r1_tarski(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | (~spl5_2 | spl5_19)),
% 3.45/0.87    inference(resolution,[],[f1514,f258])).
% 3.45/0.87  fof(f258,plain,(
% 3.45/0.87    ( ! [X2,X0,X1] : (r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(X1,X0),X2) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X2,sK0) | ~m1_subset_1(X0,sK0) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0)) ) | ~spl5_2),
% 3.45/0.87    inference(duplicate_literal_removal,[],[f257])).
% 3.45/0.87  fof(f257,plain,(
% 3.45/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X2,sK0) | r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(X1,X0),X2) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,sK0) | ~r1_tarski(X2,X0) | ~m1_subset_1(X0,sK0)) ) | ~spl5_2),
% 3.45/0.87    inference(resolution,[],[f256,f215])).
% 3.45/0.87  fof(f256,plain,(
% 3.45/0.87    ( ! [X2,X0,X1] : (~r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,X1) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X2,sK0) | r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(X0,X1),X2) | ~r1_tarski(X2,X0)) ) | ~spl5_2),
% 3.45/0.87    inference(duplicate_literal_removal,[],[f255])).
% 3.45/0.87  fof(f255,plain,(
% 3.45/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | ~r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,X1) | ~m1_subset_1(X2,sK0) | r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(X0,X1),X2) | ~m1_subset_1(X2,sK0) | ~r1_tarski(X2,X0) | ~m1_subset_1(X0,sK0)) ) | ~spl5_2),
% 3.45/0.87    inference(resolution,[],[f235,f215])).
% 3.45/0.87  fof(f235,plain,(
% 3.45/0.87    ( ! [X2,X0,X3,X1] : (~r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) | ~m1_subset_1(X1,X0) | r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),k2_tarski(X3,X2),X1)) )),
% 3.45/0.87    inference(forward_demodulation,[],[f234,f135])).
% 3.45/0.87  fof(f234,plain,(
% 3.45/0.87    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) | ~r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X3) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),k2_tarski(X3,X2),X1)) )),
% 3.45/0.87    inference(forward_demodulation,[],[f233,f135])).
% 3.45/0.87  fof(f233,plain,(
% 3.45/0.87    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,X0) | ~r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) | ~r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X3) | ~m1_subset_1(X3,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),k2_tarski(X3,X2),X1)) )),
% 3.45/0.87    inference(forward_demodulation,[],[f232,f135])).
% 3.45/0.87  fof(f232,plain,(
% 3.45/0.87    ( ! [X2,X0,X3,X1] : (~r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) | ~r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X3) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | ~m1_subset_1(X3,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),k2_tarski(X3,X2),X1)) )),
% 3.45/0.87    inference(resolution,[],[f81,f109])).
% 3.45/0.87  fof(f81,plain,(
% 3.45/0.87    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_lattice3(X0,k2_tarski(X2,X3),X1)) )),
% 3.45/0.87    inference(cnf_transformation,[],[f30])).
% 3.45/0.87  fof(f1514,plain,(
% 3.45/0.87    ~r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))) | spl5_19),
% 3.45/0.87    inference(avatar_component_clause,[],[f1512])).
% 3.45/0.87  fof(f1520,plain,(
% 3.45/0.87    ~spl5_9 | spl5_18),
% 3.45/0.87    inference(avatar_contradiction_clause,[],[f1519])).
% 3.45/0.87  fof(f1519,plain,(
% 3.45/0.87    $false | (~spl5_9 | spl5_18)),
% 3.45/0.87    inference(subsumption_resolution,[],[f1518,f1381])).
% 3.45/0.87  fof(f1518,plain,(
% 3.45/0.87    ~r2_hidden(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0) | spl5_18),
% 3.45/0.87    inference(subsumption_resolution,[],[f1517,f149])).
% 3.45/0.87  fof(f1517,plain,(
% 3.45/0.87    ~m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | ~r2_hidden(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0) | spl5_18),
% 3.45/0.87    inference(subsumption_resolution,[],[f1516,f148])).
% 3.45/0.87  fof(f1516,plain,(
% 3.45/0.87    ~m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | ~m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | ~r2_hidden(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0) | spl5_18),
% 3.45/0.87    inference(resolution,[],[f1510,f251])).
% 3.45/0.87  fof(f1510,plain,(
% 3.45/0.87    ~m1_subset_1(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0) | spl5_18),
% 3.45/0.87    inference(avatar_component_clause,[],[f1508])).
% 3.45/0.87  fof(f1515,plain,(
% 3.45/0.87    ~spl5_18 | ~spl5_19 | spl5_5 | spl5_13),
% 3.45/0.87    inference(avatar_split_clause,[],[f1506,f1476,f700,f1512,f1508])).
% 3.45/0.87  fof(f1506,plain,(
% 3.45/0.87    r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))) | ~r1_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))) | ~m1_subset_1(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0) | spl5_13),
% 3.45/0.87    inference(resolution,[],[f1478,f172])).
% 3.45/0.87  fof(f1478,plain,(
% 3.45/0.87    ~m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK0) | spl5_13),
% 3.45/0.87    inference(avatar_component_clause,[],[f1476])).
% 3.45/0.87  fof(f1495,plain,(
% 3.45/0.87    spl5_15 | ~spl5_13 | spl5_1 | ~spl5_8),
% 3.45/0.87    inference(avatar_split_clause,[],[f1490,f1376,f210,f1476,f1492])).
% 3.45/0.87  fof(f1376,plain,(
% 3.45/0.87    spl5_8 <=> r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))),
% 3.45/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 3.45/0.87  fof(f1490,plain,(
% 3.45/0.87    ~m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK0) | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | (spl5_1 | ~spl5_8)),
% 3.45/0.87    inference(forward_demodulation,[],[f1489,f135])).
% 3.45/0.87  fof(f1489,plain,(
% 3.45/0.87    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | (spl5_1 | ~spl5_8)),
% 3.45/0.87    inference(subsumption_resolution,[],[f1488,f149])).
% 3.45/0.87  fof(f1488,plain,(
% 3.45/0.87    ~m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | (spl5_1 | ~spl5_8)),
% 3.45/0.87    inference(forward_demodulation,[],[f1487,f135])).
% 3.45/0.87  fof(f1487,plain,(
% 3.45/0.87    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | (spl5_1 | ~spl5_8)),
% 3.45/0.87    inference(subsumption_resolution,[],[f1486,f211])).
% 3.45/0.87  fof(f1486,plain,(
% 3.45/0.87    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl5_8),
% 3.45/0.87    inference(subsumption_resolution,[],[f1485,f107])).
% 3.45/0.87  fof(f1485,plain,(
% 3.45/0.87    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl5_8),
% 3.45/0.87    inference(subsumption_resolution,[],[f1468,f109])).
% 3.45/0.87  fof(f1468,plain,(
% 3.45/0.87    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl5_8),
% 3.45/0.87    inference(resolution,[],[f1378,f101])).
% 3.45/0.87  fof(f1378,plain,(
% 3.45/0.87    r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~spl5_8),
% 3.45/0.87    inference(avatar_component_clause,[],[f1376])).
% 3.45/0.87  fof(f1426,plain,(
% 3.45/0.87    spl5_11),
% 3.45/0.87    inference(avatar_contradiction_clause,[],[f1425])).
% 3.45/0.87  fof(f1425,plain,(
% 3.45/0.87    $false | spl5_11),
% 3.45/0.87    inference(subsumption_resolution,[],[f1424,f148])).
% 3.45/0.87  fof(f1424,plain,(
% 3.45/0.87    ~m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | spl5_11),
% 3.45/0.87    inference(subsumption_resolution,[],[f1423,f58])).
% 3.45/0.87  fof(f1423,plain,(
% 3.45/0.87    v1_xboole_0(sK0) | ~m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | spl5_11),
% 3.45/0.87    inference(resolution,[],[f1402,f97])).
% 3.45/0.87  fof(f97,plain,(
% 3.45/0.87    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.45/0.87    inference(cnf_transformation,[],[f36])).
% 3.45/0.87  fof(f36,plain,(
% 3.45/0.87    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.45/0.87    inference(flattening,[],[f35])).
% 3.45/0.87  fof(f35,plain,(
% 3.45/0.87    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.45/0.87    inference(ennf_transformation,[],[f4])).
% 3.45/0.87  fof(f4,axiom,(
% 3.45/0.87    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.45/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 3.45/0.87  fof(f1402,plain,(
% 3.45/0.87    ~r2_hidden(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | spl5_11),
% 3.45/0.87    inference(avatar_component_clause,[],[f1400])).
% 3.45/0.87  fof(f1400,plain,(
% 3.45/0.87    spl5_11 <=> r2_hidden(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)),
% 3.45/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 3.45/0.87  fof(f1408,plain,(
% 3.45/0.87    spl5_10),
% 3.45/0.87    inference(avatar_contradiction_clause,[],[f1407])).
% 3.45/0.87  fof(f1407,plain,(
% 3.45/0.87    $false | spl5_10),
% 3.45/0.87    inference(subsumption_resolution,[],[f1406,f149])).
% 3.45/0.87  fof(f1406,plain,(
% 3.45/0.87    ~m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | spl5_10),
% 3.45/0.87    inference(subsumption_resolution,[],[f1405,f58])).
% 3.45/0.87  fof(f1405,plain,(
% 3.45/0.87    v1_xboole_0(sK0) | ~m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | spl5_10),
% 3.45/0.87    inference(resolution,[],[f1398,f97])).
% 3.45/0.87  fof(f1398,plain,(
% 3.45/0.87    ~r2_hidden(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | spl5_10),
% 3.45/0.87    inference(avatar_component_clause,[],[f1396])).
% 3.45/0.87  fof(f1396,plain,(
% 3.45/0.87    spl5_10 <=> r2_hidden(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0)),
% 3.45/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 3.45/0.87  fof(f1403,plain,(
% 3.45/0.87    ~spl5_10 | ~spl5_11 | spl5_9),
% 3.45/0.87    inference(avatar_split_clause,[],[f1393,f1380,f1400,f1396])).
% 3.45/0.87  fof(f1393,plain,(
% 3.45/0.87    ~r2_hidden(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | ~r2_hidden(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | spl5_9),
% 3.45/0.87    inference(resolution,[],[f1382,f59])).
% 3.45/0.87  fof(f59,plain,(
% 3.45/0.87    ( ! [X2,X1] : (r2_hidden(k3_xboole_0(X1,X2),sK0) | ~r2_hidden(X2,sK0) | ~r2_hidden(X1,sK0)) )),
% 3.45/0.87    inference(cnf_transformation,[],[f45])).
% 3.45/0.87  fof(f1382,plain,(
% 3.45/0.87    ~r2_hidden(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0) | spl5_9),
% 3.45/0.87    inference(avatar_component_clause,[],[f1380])).
% 3.45/0.87  fof(f1383,plain,(
% 3.45/0.87    spl5_8 | ~spl5_9 | ~spl5_2),
% 3.45/0.87    inference(avatar_split_clause,[],[f1374,f214,f1380,f1376])).
% 3.45/0.87  fof(f1374,plain,(
% 3.45/0.87    ~r2_hidden(k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0) | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~spl5_2),
% 3.45/0.87    inference(forward_demodulation,[],[f1373,f96])).
% 3.45/0.87  fof(f1373,plain,(
% 3.45/0.87    r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~r2_hidden(k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0) | ~spl5_2),
% 3.45/0.87    inference(forward_demodulation,[],[f1372,f96])).
% 3.45/0.87  fof(f1372,plain,(
% 3.45/0.87    r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~r2_hidden(k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0) | ~spl5_2),
% 3.45/0.87    inference(subsumption_resolution,[],[f1369,f149])).
% 3.45/0.87  fof(f1369,plain,(
% 3.45/0.87    r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | ~r2_hidden(k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))),sK0) | ~spl5_2),
% 3.45/0.87    inference(resolution,[],[f455,f117])).
% 3.45/0.87  fof(f455,plain,(
% 3.45/0.87    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),X0),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),X0)),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X0,sK0) | ~r2_hidden(k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),X0),sK0)) ) | ~spl5_2),
% 3.45/0.87    inference(subsumption_resolution,[],[f452,f148])).
% 3.45/0.87  fof(f452,plain,(
% 3.45/0.87    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),X0),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),X0)),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | ~r2_hidden(k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),X0),sK0)) ) | ~spl5_2),
% 3.45/0.87    inference(resolution,[],[f430,f251])).
% 3.45/0.87  fof(f430,plain,(
% 3.45/0.87    ( ! [X0] : (~m1_subset_1(k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),X0),sK0) | ~r1_tarski(k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),X0),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),k3_xboole_0(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),X0)),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))) ) | ~spl5_2),
% 3.45/0.87    inference(resolution,[],[f386,f95])).
% 3.45/0.87  fof(f386,plain,(
% 3.45/0.87    ( ! [X9] : (~r1_tarski(X9,sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X9,sK0) | ~r1_tarski(X9,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),X9),sK1(g1_orders_2(sK0,k1_yellow_1(sK0))))) ) | ~spl5_2),
% 3.45/0.87    inference(subsumption_resolution,[],[f385,f105])).
% 3.45/0.87  fof(f385,plain,(
% 3.45/0.87    ( ! [X9] : (r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),X9),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X9,sK0) | ~r1_tarski(X9,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~r1_tarski(X9,sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) ) | ~spl5_2),
% 3.45/0.87    inference(subsumption_resolution,[],[f384,f109])).
% 3.45/0.87  fof(f384,plain,(
% 3.45/0.87    ( ! [X9] : (r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),X9),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X9,sK0) | ~r1_tarski(X9,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~r1_tarski(X9,sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) ) | ~spl5_2),
% 3.45/0.87    inference(subsumption_resolution,[],[f383,f104])).
% 3.45/0.87  fof(f383,plain,(
% 3.45/0.87    ( ! [X9] : (r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),X9),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X9,sK0) | ~r1_tarski(X9,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~r1_tarski(X9,sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) ) | ~spl5_2),
% 3.45/0.87    inference(subsumption_resolution,[],[f382,f149])).
% 3.45/0.87  fof(f382,plain,(
% 3.45/0.87    ( ! [X9] : (r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),X9),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | ~m1_subset_1(X9,sK0) | ~r1_tarski(X9,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~r1_tarski(X9,sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) ) | ~spl5_2),
% 3.45/0.87    inference(subsumption_resolution,[],[f378,f148])).
% 3.45/0.87  fof(f378,plain,(
% 3.45/0.87    ( ! [X9] : (~m1_subset_1(sK2(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))),X9),sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK1(g1_orders_2(sK0,k1_yellow_1(sK0))),sK0) | ~m1_subset_1(X9,sK0) | ~r1_tarski(X9,sK1(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~r1_tarski(X9,sK2(g1_orders_2(sK0,k1_yellow_1(sK0)))) | v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) ) | ~spl5_2),
% 3.45/0.87    inference(resolution,[],[f370,f88])).
% 3.45/0.87  fof(f370,plain,(
% 3.45/0.87    ( ! [X2,X0,X1] : (r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(X0,X1)) | ~m1_subset_1(X1,sK0) | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(X0,X1),X2),X0) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X2,sK0) | ~r1_tarski(X2,X0) | ~r1_tarski(X2,X1)) ) | ~spl5_2),
% 3.45/0.87    inference(duplicate_literal_removal,[],[f366])).
% 3.45/0.87  fof(f366,plain,(
% 3.45/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK3(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(X0,X1),X2),X0) | r2_yellow_0(g1_orders_2(sK0,k1_yellow_1(sK0)),k2_tarski(X0,X1)) | ~m1_subset_1(X2,sK0) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X2,sK0) | ~m1_subset_1(X1,sK0) | ~r1_tarski(X2,X0) | ~r1_tarski(X2,X1)) ) | ~spl5_2),
% 3.45/0.87    inference(resolution,[],[f365,f258])).
% 3.45/0.87  fof(f365,plain,(
% 3.45/0.87    ( ! [X6,X4,X5,X3] : (~r1_lattice3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6) | ~m1_subset_1(X3,X4) | ~m1_subset_1(X5,X4) | r1_orders_2(g1_orders_2(X4,k1_yellow_1(X4)),sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X3) | r2_yellow_0(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5)) | ~m1_subset_1(X6,X4)) )),
% 3.45/0.87    inference(subsumption_resolution,[],[f188,f172])).
% 3.45/0.87  fof(f188,plain,(
% 3.45/0.87    ( ! [X6,X4,X5,X3] : (~m1_subset_1(X6,X4) | ~m1_subset_1(X3,X4) | ~m1_subset_1(X5,X4) | ~m1_subset_1(sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X4) | r1_orders_2(g1_orders_2(X4,k1_yellow_1(X4)),sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X3) | r2_yellow_0(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5)) | ~r1_lattice3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6)) )),
% 3.45/0.87    inference(forward_demodulation,[],[f187,f135])).
% 3.45/0.87  fof(f187,plain,(
% 3.45/0.87    ( ! [X6,X4,X5,X3] : (~m1_subset_1(X3,X4) | ~m1_subset_1(X5,X4) | ~m1_subset_1(sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X4) | r1_orders_2(g1_orders_2(X4,k1_yellow_1(X4)),sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X3) | r2_yellow_0(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5)) | ~r1_lattice3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6) | ~m1_subset_1(X6,u1_struct_0(g1_orders_2(X4,k1_yellow_1(X4))))) )),
% 3.45/0.87    inference(subsumption_resolution,[],[f186,f105])).
% 3.45/0.87  fof(f186,plain,(
% 3.45/0.87    ( ! [X6,X4,X5,X3] : (~m1_subset_1(X3,X4) | ~m1_subset_1(X5,X4) | ~m1_subset_1(sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X4) | r1_orders_2(g1_orders_2(X4,k1_yellow_1(X4)),sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X3) | r2_yellow_0(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5)) | ~r1_lattice3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6) | ~m1_subset_1(X6,u1_struct_0(g1_orders_2(X4,k1_yellow_1(X4)))) | ~v5_orders_2(g1_orders_2(X4,k1_yellow_1(X4)))) )),
% 3.45/0.87    inference(subsumption_resolution,[],[f182,f109])).
% 3.45/0.87  fof(f182,plain,(
% 3.45/0.87    ( ! [X6,X4,X5,X3] : (~m1_subset_1(X3,X4) | ~m1_subset_1(X5,X4) | ~m1_subset_1(sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X4) | r1_orders_2(g1_orders_2(X4,k1_yellow_1(X4)),sK3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6),X3) | r2_yellow_0(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5)) | ~r1_lattice3(g1_orders_2(X4,k1_yellow_1(X4)),k2_tarski(X3,X5),X6) | ~m1_subset_1(X6,u1_struct_0(g1_orders_2(X4,k1_yellow_1(X4)))) | ~l1_orders_2(g1_orders_2(X4,k1_yellow_1(X4))) | ~v5_orders_2(g1_orders_2(X4,k1_yellow_1(X4)))) )),
% 3.45/0.87    inference(resolution,[],[f176,f93])).
% 3.45/0.87  fof(f176,plain,(
% 3.45/0.87    ( ! [X2,X0,X3,X1] : (~r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),k2_tarski(X1,X2),X3) | ~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X3,X0) | r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X3,X1)) )),
% 3.45/0.87    inference(forward_demodulation,[],[f175,f135])).
% 3.45/0.87  fof(f175,plain,(
% 3.45/0.87    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | ~r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),k2_tarski(X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X3,X1)) )),
% 3.45/0.87    inference(forward_demodulation,[],[f174,f135])).
% 3.45/0.87  fof(f174,plain,(
% 3.45/0.87    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,X0) | ~r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),k2_tarski(X1,X2),X3) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | ~m1_subset_1(X3,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X3,X1)) )),
% 3.45/0.87    inference(forward_demodulation,[],[f173,f135])).
% 3.45/0.87  fof(f173,plain,(
% 3.45/0.87    ( ! [X2,X0,X3,X1] : (~r1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)),k2_tarski(X1,X2),X3) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | ~m1_subset_1(X3,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | r1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X3,X1)) )),
% 3.45/0.87    inference(resolution,[],[f79,f109])).
% 3.45/0.87  fof(f79,plain,(
% 3.45/0.87    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~r1_lattice3(X0,k2_tarski(X2,X3),X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2)) )),
% 3.45/0.87    inference(cnf_transformation,[],[f30])).
% 3.45/0.87  fof(f336,plain,(
% 3.45/0.87    ~spl5_1),
% 3.45/0.87    inference(avatar_contradiction_clause,[],[f335])).
% 3.45/0.87  fof(f335,plain,(
% 3.45/0.87    $false | ~spl5_1),
% 3.45/0.87    inference(subsumption_resolution,[],[f334,f58])).
% 3.45/0.87  fof(f334,plain,(
% 3.45/0.87    v1_xboole_0(sK0) | ~spl5_1),
% 3.45/0.87    inference(resolution,[],[f212,f112])).
% 3.45/0.87  fof(f112,plain,(
% 3.45/0.87    ( ! [X0] : (~v2_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 3.45/0.87    inference(definition_unfolding,[],[f73,f61])).
% 3.45/0.87  fof(f73,plain,(
% 3.45/0.87    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 3.45/0.87    inference(cnf_transformation,[],[f23])).
% 3.45/0.87  fof(f23,plain,(
% 3.45/0.87    ! [X0] : ((v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0))),
% 3.45/0.87    inference(ennf_transformation,[],[f16])).
% 3.45/0.87  fof(f16,axiom,(
% 3.45/0.87    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 3.45/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).
% 3.45/0.87  fof(f212,plain,(
% 3.45/0.87    v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl5_1),
% 3.45/0.87    inference(avatar_component_clause,[],[f210])).
% 3.45/0.87  fof(f216,plain,(
% 3.45/0.87    spl5_1 | spl5_2),
% 3.45/0.87    inference(avatar_split_clause,[],[f208,f214,f210])).
% 3.45/0.87  fof(f208,plain,(
% 3.45/0.87    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | ~r1_tarski(X1,X0) | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 3.45/0.87    inference(duplicate_literal_removal,[],[f207])).
% 3.45/0.87  fof(f207,plain,(
% 3.45/0.87    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | ~r1_tarski(X1,X0) | ~m1_subset_1(X1,sK0) | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 3.45/0.87    inference(forward_demodulation,[],[f206,f135])).
% 3.45/0.87  fof(f206,plain,(
% 3.45/0.87    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | ~r1_tarski(X1,X0) | ~m1_subset_1(X1,sK0) | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 3.45/0.87    inference(duplicate_literal_removal,[],[f205])).
% 3.45/0.87  fof(f205,plain,(
% 3.45/0.87    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | ~m1_subset_1(X0,sK0) | ~r1_tarski(X1,X0) | ~m1_subset_1(X1,sK0) | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 3.45/0.87    inference(forward_demodulation,[],[f204,f135])).
% 3.45/0.87  fof(f204,plain,(
% 3.45/0.87    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | ~r1_tarski(X1,X0) | ~m1_subset_1(X1,sK0) | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) | ~m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 3.45/0.87    inference(subsumption_resolution,[],[f203,f107])).
% 3.45/0.87  fof(f203,plain,(
% 3.45/0.87    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | ~r1_tarski(X1,X0) | ~m1_subset_1(X1,sK0) | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) | ~m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 3.45/0.87    inference(subsumption_resolution,[],[f202,f109])).
% 3.45/0.87  fof(f202,plain,(
% 3.45/0.87    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | ~r1_tarski(X1,X0) | ~m1_subset_1(X1,sK0) | r1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) | ~m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 3.45/0.87    inference(resolution,[],[f201,f100])).
% 3.45/0.87  fof(f100,plain,(
% 3.45/0.87    ( ! [X2,X0,X1] : (~r3_orders_2(X0,X1,X2) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.45/0.87    inference(cnf_transformation,[],[f57])).
% 3.45/0.87  fof(f201,plain,(
% 3.45/0.87    ( ! [X0,X1] : (r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,X0) | ~m1_subset_1(X0,sK0) | ~r1_tarski(X1,X0) | ~m1_subset_1(X1,sK0)) )),
% 3.45/0.87    inference(resolution,[],[f200,f58])).
% 3.45/0.87  fof(f200,plain,(
% 3.45/0.87    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X2,X0) | r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X1,X0)) )),
% 3.45/0.87    inference(forward_demodulation,[],[f199,f135])).
% 3.45/0.87  fof(f199,plain,(
% 3.45/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | v1_xboole_0(X0)) )),
% 3.45/0.87    inference(forward_demodulation,[],[f114,f135])).
% 3.45/0.87  fof(f114,plain,(
% 3.45/0.87    ( ! [X2,X0,X1] : (r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | v1_xboole_0(X0)) )),
% 3.45/0.87    inference(definition_unfolding,[],[f77,f61,f61,f61])).
% 3.45/0.87  fof(f77,plain,(
% 3.45/0.87    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 3.45/0.87    inference(cnf_transformation,[],[f46])).
% 3.45/0.87  % SZS output end Proof for theBenchmark
% 3.45/0.87  % (15149)------------------------------
% 3.45/0.87  % (15149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.45/0.87  % (15149)Termination reason: Refutation
% 3.45/0.87  
% 3.45/0.87  % (15149)Memory used [KB]: 12792
% 3.45/0.87  % (15149)Time elapsed: 0.445 s
% 3.45/0.87  % (15149)------------------------------
% 3.45/0.87  % (15149)------------------------------
% 3.45/0.87  % (15145)Success in time 0.515 s
%------------------------------------------------------------------------------
