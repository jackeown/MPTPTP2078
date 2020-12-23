%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1593+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:10 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   44 (  85 expanded)
%              Number of leaves         :    8 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :   85 ( 151 expanded)
%              Number of equality atoms :   44 (  72 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f52,f68])).

fof(f68,plain,(
    spl1_2 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | spl1_2 ),
    inference(trivial_inequality_removal,[],[f66])).

fof(f66,plain,
    ( sK0 != sK0
    | spl1_2 ),
    inference(superposition,[],[f31,f63])).

fof(f63,plain,(
    ! [X0] : u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X0 ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2)
      | u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X1 ) ),
    inference(superposition,[],[f37,f35])).

fof(f35,plain,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) ),
    inference(global_subsumption,[],[f22,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))
      | g1_orders_2(X0,k1_yellow_1(X0)) = g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) ) ),
    inference(resolution,[],[f18,f23])).

fof(f23,plain,(
    ! [X0] : v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f15,f14])).

fof(f14,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

fof(f15,plain,(
    ! [X0] : v1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
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

fof(f22,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f16,f14])).

fof(f16,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X4,X5,X3] :
      ( g1_orders_2(u1_struct_0(g1_orders_2(X3,k1_yellow_1(X3))),u1_orders_2(g1_orders_2(X3,k1_yellow_1(X3)))) != g1_orders_2(X4,X5)
      | u1_struct_0(g1_orders_2(X3,k1_yellow_1(X3))) = X4 ) ),
    inference(resolution,[],[f33,f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f33,plain,(
    ! [X0] : m1_subset_1(u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))))) ),
    inference(resolution,[],[f17,f22])).

fof(f17,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f31,plain,
    ( sK0 != u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl1_2
  <=> sK0 = u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f52,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f51])).

fof(f51,plain,
    ( $false
    | spl1_1 ),
    inference(trivial_inequality_removal,[],[f50])).

fof(f50,plain,
    ( k1_yellow_1(sK0) != k1_yellow_1(sK0)
    | spl1_1 ),
    inference(superposition,[],[f27,f42])).

fof(f42,plain,(
    ! [X0] : k1_yellow_1(X0) = u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2)
      | u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = X2 ) ),
    inference(superposition,[],[f36,f35])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) != g1_orders_2(X1,X2)
      | u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = X2 ) ),
    inference(resolution,[],[f33,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f27,plain,
    ( k1_yellow_1(sK0) != u1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl1_1
  <=> k1_yellow_1(sK0) = u1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f32,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f21,f29,f25])).

fof(f21,plain,
    ( sK0 != u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | k1_yellow_1(sK0) != u1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(definition_unfolding,[],[f13,f14,f14])).

fof(f13,plain,
    ( sK0 != u1_struct_0(k2_yellow_1(sK0))
    | k1_yellow_1(sK0) != u1_orders_2(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( k1_yellow_1(X0) != u1_orders_2(k2_yellow_1(X0))
      | u1_struct_0(k2_yellow_1(X0)) != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0))
        & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0))
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

%------------------------------------------------------------------------------
