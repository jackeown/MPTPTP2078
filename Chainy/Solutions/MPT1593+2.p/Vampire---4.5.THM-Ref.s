%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1593+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:26 EST 2020

% Result     : Theorem 3.89s
% Output     : Refutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :   42 (  71 expanded)
%              Number of leaves         :   10 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   84 ( 137 expanded)
%              Number of equality atoms :   44 (  64 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6260,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5237,f6212,f6258])).

fof(f6258,plain,(
    spl223_3 ),
    inference(avatar_contradiction_clause,[],[f6228])).

fof(f6228,plain,
    ( $false
    | spl223_3 ),
    inference(unit_resulting_resolution,[],[f5174,f6223])).

fof(f6223,plain,
    ( ! [X0] : k2_yellow_1(sK2) != g1_orders_2(X0,k1_wellord2(sK2))
    | spl223_3 ),
    inference(forward_demodulation,[],[f6219,f5714])).

fof(f5714,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(u1_struct_0(k2_yellow_1(X0)),u1_orders_2(k2_yellow_1(X0))) ),
    inference(unit_resulting_resolution,[],[f4038,f4037,f4299])).

fof(f4299,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3213])).

fof(f3213,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3212])).

fof(f3212,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1859])).

fof(f1859,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(f4037,plain,(
    ! [X0] : v1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3076])).

fof(f3076,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f4038,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3076])).

fof(f6219,plain,
    ( ! [X0] : g1_orders_2(u1_struct_0(k2_yellow_1(sK2)),u1_orders_2(k2_yellow_1(sK2))) != g1_orders_2(X0,k1_wellord2(sK2))
    | spl223_3 ),
    inference(unit_resulting_resolution,[],[f5236,f5288,f4260])).

fof(f4260,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f3190])).

fof(f3190,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f1926])).

fof(f1926,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f5288,plain,(
    ! [X0] : m1_subset_1(u1_orders_2(k2_yellow_1(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))))) ),
    inference(unit_resulting_resolution,[],[f4038,f4027])).

fof(f4027,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3095])).

fof(f3095,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1905])).

fof(f1905,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f5236,plain,
    ( u1_orders_2(k2_yellow_1(sK2)) != k1_wellord2(sK2)
    | spl223_3 ),
    inference(avatar_component_clause,[],[f5234])).

fof(f5234,plain,
    ( spl223_3
  <=> u1_orders_2(k2_yellow_1(sK2)) = k1_wellord2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl223_3])])).

fof(f5174,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_wellord2(X0)) ),
    inference(backward_demodulation,[],[f4033,f4034])).

fof(f4034,plain,(
    ! [X0] : k1_wellord2(X0) = k1_yellow_1(X0) ),
    inference(cnf_transformation,[],[f3079])).

fof(f3079,axiom,(
    ! [X0] : k1_wellord2(X0) = k1_yellow_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_yellow_1)).

fof(f4033,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3074])).

fof(f3074,axiom,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

fof(f6212,plain,(
    spl223_2 ),
    inference(avatar_contradiction_clause,[],[f6182])).

fof(f6182,plain,
    ( $false
    | spl223_2 ),
    inference(unit_resulting_resolution,[],[f5174,f6178])).

fof(f6178,plain,
    ( ! [X0] : k2_yellow_1(sK2) != g1_orders_2(sK2,X0)
    | spl223_2 ),
    inference(forward_demodulation,[],[f6166,f5714])).

fof(f6166,plain,
    ( ! [X0] : g1_orders_2(sK2,X0) != g1_orders_2(u1_struct_0(k2_yellow_1(sK2)),u1_orders_2(k2_yellow_1(sK2)))
    | spl223_2 ),
    inference(unit_resulting_resolution,[],[f5232,f5288,f4259])).

fof(f4259,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f3190])).

fof(f5232,plain,
    ( sK2 != u1_struct_0(k2_yellow_1(sK2))
    | spl223_2 ),
    inference(avatar_component_clause,[],[f5230])).

fof(f5230,plain,
    ( spl223_2
  <=> sK2 = u1_struct_0(k2_yellow_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl223_2])])).

fof(f5237,plain,
    ( ~ spl223_2
    | ~ spl223_3 ),
    inference(avatar_split_clause,[],[f5173,f5234,f5230])).

fof(f5173,plain,
    ( u1_orders_2(k2_yellow_1(sK2)) != k1_wellord2(sK2)
    | sK2 != u1_struct_0(k2_yellow_1(sK2)) ),
    inference(backward_demodulation,[],[f4024,f4034])).

fof(f4024,plain,
    ( k1_yellow_1(sK2) != u1_orders_2(k2_yellow_1(sK2))
    | sK2 != u1_struct_0(k2_yellow_1(sK2)) ),
    inference(cnf_transformation,[],[f3617])).

fof(f3617,plain,
    ( k1_yellow_1(sK2) != u1_orders_2(k2_yellow_1(sK2))
    | sK2 != u1_struct_0(k2_yellow_1(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f3093,f3616])).

fof(f3616,plain,
    ( ? [X0] :
        ( k1_yellow_1(X0) != u1_orders_2(k2_yellow_1(X0))
        | u1_struct_0(k2_yellow_1(X0)) != X0 )
   => ( k1_yellow_1(sK2) != u1_orders_2(k2_yellow_1(sK2))
      | sK2 != u1_struct_0(k2_yellow_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f3093,plain,(
    ? [X0] :
      ( k1_yellow_1(X0) != u1_orders_2(k2_yellow_1(X0))
      | u1_struct_0(k2_yellow_1(X0)) != X0 ) ),
    inference(ennf_transformation,[],[f3081])).

fof(f3081,negated_conjecture,(
    ~ ! [X0] :
        ( k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0))
        & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    inference(negated_conjecture,[],[f3080])).

fof(f3080,conjecture,(
    ! [X0] :
      ( k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0))
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
%------------------------------------------------------------------------------
