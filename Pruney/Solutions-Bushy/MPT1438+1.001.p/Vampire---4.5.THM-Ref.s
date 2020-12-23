%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1438+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:55 EST 2020

% Result     : Theorem 3.07s
% Output     : Refutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :  219 (1374 expanded)
%              Number of leaves         :   33 ( 290 expanded)
%              Depth                    :   24
%              Number of atoms          :  715 (6032 expanded)
%              Number of equality atoms :   84 (2093 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4078,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f171,f209,f1422,f1453,f1913,f1919,f1987,f2885,f3053,f3057,f3083,f3164,f3567,f3662,f4073,f4077])).

fof(f4077,plain,
    ( spl10_4
    | ~ spl10_16 ),
    inference(avatar_contradiction_clause,[],[f4075])).

fof(f4075,plain,
    ( $false
    | spl10_4
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f205,f1924])).

fof(f1924,plain,
    ( sP9(sK0)
    | ~ spl10_16 ),
    inference(resolution,[],[f1431,f85])).

fof(f85,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP9(X0) ) ),
    inference(cnf_transformation,[],[f85_D])).

fof(f85_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,u1_struct_0(X0))
    <=> ~ sP9(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f1431,plain,
    ( m1_subset_1(sK6(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f1430])).

fof(f1430,plain,
    ( spl10_16
  <=> m1_subset_1(sK6(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f205,plain,
    ( ~ sP9(sK0)
    | spl10_4 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl10_4
  <=> sP9(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f4073,plain,
    ( ~ spl10_5
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(avatar_contradiction_clause,[],[f4071])).

fof(f4071,plain,
    ( $false
    | ~ spl10_5
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f1431,f4067])).

fof(f4067,plain,
    ( ~ m1_subset_1(sK6(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl10_5
    | ~ spl10_13
    | ~ spl10_30 ),
    inference(resolution,[],[f3664,f2884])).

fof(f2884,plain,
    ( ! [X1] :
        ( ~ r3_lattices(sK0,X1,sK6(k8_filter_1(sK0),u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f2883])).

fof(f2883,plain,
    ( spl10_30
  <=> ! [X1] :
        ( ~ r3_lattices(sK0,X1,sK6(k8_filter_1(sK0),u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f3664,plain,
    ( r3_lattices(sK0,sK6(k8_filter_1(sK0),u1_struct_0(sK0)),sK6(k8_filter_1(sK0),u1_struct_0(sK0)))
    | ~ spl10_5
    | ~ spl10_13 ),
    inference(resolution,[],[f1417,f680])).

fof(f680,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | r3_lattices(sK0,X0,X0) )
    | ~ spl10_5 ),
    inference(resolution,[],[f208,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f208,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r3_lattices(sK0,X6,X6) )
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl10_5
  <=> ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r3_lattices(sK0,X6,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f1417,plain,
    ( r2_hidden(sK6(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f1416])).

fof(f1416,plain,
    ( spl10_13
  <=> r2_hidden(sK6(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f3662,plain,
    ( spl10_13
    | ~ spl10_28 ),
    inference(avatar_contradiction_clause,[],[f3660])).

fof(f3660,plain,
    ( $false
    | spl10_13
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f1418,f2895])).

fof(f2895,plain,
    ( r2_hidden(sK6(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl10_28 ),
    inference(resolution,[],[f1912,f935])).

fof(f935,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k8_filter_1(sK0))
      | r2_hidden(X5,u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f921])).

fof(f921,plain,(
    ! [X4,X5] :
      ( r2_hidden(X5,u1_struct_0(sK0))
      | ~ r2_hidden(k4_tarski(X4,X5),k8_filter_1(sK0))
      | ~ r2_hidden(k4_tarski(X4,X5),k8_filter_1(sK0)) ) ),
    inference(superposition,[],[f736,f918])).

fof(f918,plain,(
    ! [X0,X1] :
      ( sK2(k4_tarski(X0,X1),sK0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK0)) ) ),
    inference(equality_resolution,[],[f772])).

fof(f772,plain,(
    ! [X6,X8,X7] :
      ( k4_tarski(X7,X8) != X6
      | sK2(X6,sK0) = X8
      | ~ r2_hidden(X6,k8_filter_1(sK0)) ) ),
    inference(superposition,[],[f78,f767])).

fof(f767,plain,(
    ! [X2] :
      ( k4_tarski(sK1(X2,sK0),sK2(X2,sK0)) = X2
      | ~ r2_hidden(X2,k8_filter_1(sK0)) ) ),
    inference(global_subsumption,[],[f174,f200,f201,f766])).

fof(f766,plain,(
    ! [X2] :
      ( k4_tarski(sK1(X2,sK0),sK2(X2,sK0)) = X2
      | ~ r2_hidden(X2,k8_filter_1(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(sK1(X2,sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2(X2,sK0),u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f762])).

fof(f762,plain,(
    ! [X2] :
      ( k4_tarski(sK1(X2,sK0),sK2(X2,sK0)) = X2
      | ~ r2_hidden(X2,k8_filter_1(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(sK1(X2,sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2(X2,sK0),u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f755,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X3,X1)
      | k4_tarski(X2,X3) = k1_domain_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X2,X3) = k1_domain_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X2,X3) = k1_domain_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X1)
        & m1_subset_1(X2,X0)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => k4_tarski(X2,X3) = k1_domain_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_domain_1)).

fof(f755,plain,(
    ! [X2] :
      ( k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1(X2,sK0),sK2(X2,sK0)) = X2
      | ~ r2_hidden(X2,k8_filter_1(sK0)) ) ),
    inference(forward_demodulation,[],[f106,f103])).

fof(f103,plain,(
    k8_filter_1(sK0) = a_1_0_filter_1(sK0) ),
    inference(global_subsumption,[],[f46,f45,f92])).

fof(f92,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | k8_filter_1(sK0) = a_1_0_filter_1(sK0) ),
    inference(resolution,[],[f44,f59])).

fof(f59,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | k8_filter_1(X0) = a_1_0_filter_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k8_filter_1(X0) = a_1_0_filter_1(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k8_filter_1(X0) = a_1_0_filter_1(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k8_filter_1(X0) = a_1_0_filter_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_filter_1)).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ( u1_struct_0(X0) != k3_relat_1(k8_filter_1(X0))
        | u1_struct_0(X0) != k2_relat_1(k8_filter_1(X0))
        | u1_struct_0(X0) != k1_relat_1(k8_filter_1(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ( u1_struct_0(X0) != k3_relat_1(k8_filter_1(X0))
        | u1_struct_0(X0) != k2_relat_1(k8_filter_1(X0))
        | u1_struct_0(X0) != k1_relat_1(k8_filter_1(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( u1_struct_0(X0) = k3_relat_1(k8_filter_1(X0))
          & u1_struct_0(X0) = k2_relat_1(k8_filter_1(X0))
          & u1_struct_0(X0) = k1_relat_1(k8_filter_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( u1_struct_0(X0) = k3_relat_1(k8_filter_1(X0))
        & u1_struct_0(X0) = k2_relat_1(k8_filter_1(X0))
        & u1_struct_0(X0) = k1_relat_1(k8_filter_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_filter_1)).

fof(f45,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f106,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,a_1_0_filter_1(sK0))
      | k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1(X2,sK0),sK2(X2,sK0)) = X2 ) ),
    inference(global_subsumption,[],[f46,f45,f95])).

fof(f95,plain,(
    ! [X2] :
      ( ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1(X2,sK0),sK2(X2,sK0)) = X2
      | ~ r2_hidden(X2,a_1_0_filter_1(sK0)) ) ),
    inference(resolution,[],[f44,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),sK1(X0,X1),sK2(X0,X1)) = X0
      | ~ r2_hidden(X0,a_1_0_filter_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,a_1_0_filter_1(X1))
      <=> ? [X2,X3] :
            ( r3_lattices(X1,X2,X3)
            & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X1))
            & m1_subset_1(X2,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,a_1_0_filter_1(X1))
      <=> ? [X2,X3] :
            ( r3_lattices(X1,X2,X3)
            & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X1))
            & m1_subset_1(X2,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_1_0_filter_1(X1))
      <=> ? [X2,X3] :
            ( r3_lattices(X1,X2,X3)
            & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X1))
            & m1_subset_1(X2,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_1_0_filter_1)).

fof(f201,plain,(
    ! [X1] :
      ( m1_subset_1(sK2(X1,sK0),u1_struct_0(sK0))
      | ~ r2_hidden(X1,k8_filter_1(sK0)) ) ),
    inference(forward_demodulation,[],[f105,f103])).

fof(f105,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,a_1_0_filter_1(sK0))
      | m1_subset_1(sK2(X1,sK0),u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f46,f45,f94])).

fof(f94,plain,(
    ! [X1] :
      ( ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | m1_subset_1(sK2(X1,sK0),u1_struct_0(sK0))
      | ~ r2_hidden(X1,a_1_0_filter_1(sK0)) ) ),
    inference(resolution,[],[f44,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_1_0_filter_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f200,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0,sK0),u1_struct_0(sK0))
      | ~ r2_hidden(X0,k8_filter_1(sK0)) ) ),
    inference(forward_demodulation,[],[f104,f103])).

fof(f104,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0,sK0),u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_1_0_filter_1(sK0)) ) ),
    inference(global_subsumption,[],[f46,f45,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | m1_subset_1(sK1(X0,sK0),u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_1_0_filter_1(sK0)) ) ),
    inference(resolution,[],[f44,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | m1_subset_1(sK1(X0,X1),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_1_0_filter_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f174,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(global_subsumption,[],[f90,f172])).

fof(f172,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f130,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ l2_lattices(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l2_lattices(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l2_lattices(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l2_lattices)).

fof(f130,plain,(
    l2_lattices(sK0) ),
    inference(resolution,[],[f46,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f90,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f44,f57])).

fof(f57,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X2,X3) != k4_tarski(X0,X1)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k4_tarski(X2,X3) != k4_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X2,X3) = k4_tarski(X0,X1)
     => ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_zfmisc_1)).

fof(f736,plain,(
    ! [X14] :
      ( r2_hidden(sK2(X14,sK0),u1_struct_0(sK0))
      | ~ r2_hidden(X14,k8_filter_1(sK0)) ) ),
    inference(global_subsumption,[],[f720])).

fof(f720,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k8_filter_1(sK0))
      | r2_hidden(sK2(X0,sK0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f201,f180])).

fof(f180,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | r2_hidden(X6,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f174,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f1912,plain,
    ( r2_hidden(k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK6(k8_filter_1(sK0),u1_struct_0(sK0))),k8_filter_1(sK0))
    | ~ spl10_28 ),
    inference(avatar_component_clause,[],[f1910])).

fof(f1910,plain,
    ( spl10_28
  <=> r2_hidden(k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK6(k8_filter_1(sK0),u1_struct_0(sK0))),k8_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f1418,plain,
    ( ~ r2_hidden(sK6(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | spl10_13 ),
    inference(avatar_component_clause,[],[f1416])).

fof(f3567,plain,
    ( spl10_17
    | ~ spl10_29 ),
    inference(avatar_contradiction_clause,[],[f3565])).

fof(f3565,plain,
    ( $false
    | spl10_17
    | ~ spl10_29 ),
    inference(subsumption_resolution,[],[f1449,f3548])).

fof(f3548,plain,
    ( r2_hidden(sK3(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl10_29 ),
    inference(resolution,[],[f1986,f813])).

fof(f813,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k8_filter_1(sK0))
      | r2_hidden(X2,u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f797])).

fof(f797,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,u1_struct_0(sK0))
      | ~ r2_hidden(k4_tarski(X2,X3),k8_filter_1(sK0))
      | ~ r2_hidden(k4_tarski(X2,X3),k8_filter_1(sK0)) ) ),
    inference(superposition,[],[f584,f795])).

fof(f795,plain,(
    ! [X0,X1] :
      ( sK1(k4_tarski(X0,X1),sK0) = X0
      | ~ r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK0)) ) ),
    inference(equality_resolution,[],[f770])).

fof(f770,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | sK1(X0,sK0) = X1
      | ~ r2_hidden(X0,k8_filter_1(sK0)) ) ),
    inference(superposition,[],[f77,f767])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X2,X3) != k4_tarski(X0,X1)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f584,plain,(
    ! [X13] :
      ( r2_hidden(sK1(X13,sK0),u1_struct_0(sK0))
      | ~ r2_hidden(X13,k8_filter_1(sK0)) ) ),
    inference(global_subsumption,[],[f199])).

fof(f199,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k8_filter_1(sK0))
      | r2_hidden(sK1(X2,sK0),u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f44,f45,f46,f198])).

fof(f198,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k8_filter_1(sK0))
      | r2_hidden(sK1(X2,sK0),u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(forward_demodulation,[],[f195,f103])).

fof(f195,plain,(
    ! [X2] :
      ( r2_hidden(sK1(X2,sK0),u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ r2_hidden(X2,a_1_0_filter_1(sK0)) ) ),
    inference(resolution,[],[f180,f63])).

fof(f1986,plain,
    ( r2_hidden(k4_tarski(sK3(k8_filter_1(sK0),u1_struct_0(sK0)),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),k8_filter_1(sK0))
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f1984])).

fof(f1984,plain,
    ( spl10_29
  <=> r2_hidden(k4_tarski(sK3(k8_filter_1(sK0),u1_struct_0(sK0)),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),k8_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f1449,plain,
    ( ~ r2_hidden(sK3(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | spl10_17 ),
    inference(avatar_component_clause,[],[f1447])).

fof(f1447,plain,
    ( spl10_17
  <=> r2_hidden(sK3(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f3164,plain,
    ( spl10_1
    | ~ spl10_3
    | ~ spl10_32 ),
    inference(avatar_contradiction_clause,[],[f3162])).

fof(f3162,plain,
    ( $false
    | spl10_1
    | ~ spl10_3
    | ~ spl10_32 ),
    inference(subsumption_resolution,[],[f162,f3159])).

fof(f3159,plain,
    ( u1_struct_0(sK0) = k3_relat_1(k8_filter_1(sK0))
    | ~ spl10_3
    | ~ spl10_32 ),
    inference(forward_demodulation,[],[f3137,f60])).

fof(f60,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f3137,plain,
    ( k3_relat_1(k8_filter_1(sK0)) = k2_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl10_3
    | ~ spl10_32 ),
    inference(backward_demodulation,[],[f3052,f169])).

fof(f169,plain,
    ( u1_struct_0(sK0) = k1_relat_1(k8_filter_1(sK0))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl10_3
  <=> u1_struct_0(sK0) = k1_relat_1(k8_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f3052,plain,
    ( k3_relat_1(k8_filter_1(sK0)) = k2_xboole_0(k1_relat_1(k8_filter_1(sK0)),u1_struct_0(sK0))
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f3050])).

fof(f3050,plain,
    ( spl10_32
  <=> k3_relat_1(k8_filter_1(sK0)) = k2_xboole_0(k1_relat_1(k8_filter_1(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f162,plain,
    ( u1_struct_0(sK0) != k3_relat_1(k8_filter_1(sK0))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl10_1
  <=> u1_struct_0(sK0) = k3_relat_1(k8_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f3083,plain,
    ( ~ spl10_2
    | ~ spl10_17
    | ~ spl10_18 ),
    inference(avatar_contradiction_clause,[],[f3081])).

fof(f3081,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_17
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f1448,f2959])).

fof(f2959,plain,
    ( ~ r2_hidden(sK3(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl10_2
    | ~ spl10_18 ),
    inference(backward_demodulation,[],[f2823,f165])).

fof(f165,plain,
    ( u1_struct_0(sK0) = k2_relat_1(k8_filter_1(sK0))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl10_2
  <=> u1_struct_0(sK0) = k2_relat_1(k8_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f2823,plain,
    ( ~ r2_hidden(sK3(k8_filter_1(sK0),u1_struct_0(sK0)),k2_relat_1(k8_filter_1(sK0)))
    | ~ spl10_18 ),
    inference(resolution,[],[f2792,f1452])).

fof(f1452,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK3(k8_filter_1(sK0),u1_struct_0(sK0)),X0),k8_filter_1(sK0))
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f1451])).

fof(f1451,plain,
    ( spl10_18
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK3(k8_filter_1(sK0),u1_struct_0(sK0)),X0),k8_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f2792,plain,(
    ! [X15] :
      ( r2_hidden(k4_tarski(X15,X15),k8_filter_1(sK0))
      | ~ r2_hidden(X15,k2_relat_1(k8_filter_1(sK0))) ) ),
    inference(resolution,[],[f2687,f83])).

fof(f83,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK7(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f2687,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK0))
      | r2_hidden(k4_tarski(X1,X1),k8_filter_1(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f2686])).

fof(f2686,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,X1),k8_filter_1(sK0))
      | ~ r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK0))
      | ~ r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK0)) ) ),
    inference(superposition,[],[f2540,f918])).

fof(f2540,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK2(X0,sK0),sK2(X0,sK0)),k8_filter_1(sK0))
      | ~ r2_hidden(X0,k8_filter_1(sK0)) ) ),
    inference(global_subsumption,[],[f201,f174,f2538])).

fof(f2538,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK2(X0,sK0),sK2(X0,sK0)),k8_filter_1(sK0))
      | ~ r2_hidden(X0,k8_filter_1(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(sK2(X0,sK0),u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f2533])).

fof(f2533,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK2(X0,sK0),sK2(X0,sK0)),k8_filter_1(sK0))
      | ~ r2_hidden(X0,k8_filter_1(sK0))
      | ~ r2_hidden(X0,k8_filter_1(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(sK2(X0,sK0),u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f759,f735])).

fof(f735,plain,(
    ! [X12,X13,X11] :
      ( k4_tarski(sK2(X11,sK0),X13) = k1_domain_1(u1_struct_0(sK0),X12,sK2(X11,sK0),X13)
      | ~ r2_hidden(X11,k8_filter_1(sK0))
      | v1_xboole_0(X12)
      | ~ m1_subset_1(X13,X12) ) ),
    inference(global_subsumption,[],[f174,f727])).

fof(f727,plain,(
    ! [X12,X13,X11] :
      ( ~ r2_hidden(X11,k8_filter_1(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(X12)
      | ~ m1_subset_1(X13,X12)
      | k4_tarski(sK2(X11,sK0),X13) = k1_domain_1(u1_struct_0(sK0),X12,sK2(X11,sK0),X13) ) ),
    inference(resolution,[],[f201,f79])).

fof(f759,plain,(
    ! [X0] :
      ( r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2(X0,sK0),sK2(X0,sK0)),k8_filter_1(sK0))
      | ~ r2_hidden(X0,k8_filter_1(sK0)) ) ),
    inference(global_subsumption,[],[f44,f45,f46,f201,f758])).

fof(f758,plain,(
    ! [X0] :
      ( r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2(X0,sK0),sK2(X0,sK0)),k8_filter_1(sK0))
      | ~ r2_hidden(X0,k8_filter_1(sK0))
      | v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(sK2(X0,sK0),u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f757,f103])).

fof(f757,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k8_filter_1(sK0))
      | v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(sK2(X0,sK0),u1_struct_0(sK0))
      | r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2(X0,sK0),sK2(X0,sK0)),a_1_0_filter_1(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f756])).

fof(f756,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k8_filter_1(sK0))
      | v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(sK2(X0,sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2(X0,sK0),u1_struct_0(sK0))
      | r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2(X0,sK0),sK2(X0,sK0)),a_1_0_filter_1(sK0)) ) ),
    inference(resolution,[],[f733,f80])).

fof(f80,plain,(
    ! [X2,X3,X1] :
      ( v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r3_lattices(X1,X2,X3)
      | r2_hidden(k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3),a_1_0_filter_1(X1)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) != X0
      | ~ r3_lattices(X1,X2,X3)
      | r2_hidden(X0,a_1_0_filter_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f733,plain,(
    ! [X7] :
      ( r3_lattices(sK0,sK2(X7,sK0),sK2(X7,sK0))
      | ~ r2_hidden(X7,k8_filter_1(sK0)) ) ),
    inference(global_subsumption,[],[f44,f46,f99,f100,f101,f577,f725])).

fof(f725,plain,(
    ! [X7] :
      ( ~ r2_hidden(X7,k8_filter_1(sK0))
      | v2_struct_0(sK0)
      | ~ v6_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ l3_lattices(sK0)
      | r3_lattices(sK0,sK2(X7,sK0),sK2(X7,sK0))
      | ~ sP9(sK0) ) ),
    inference(resolution,[],[f201,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_lattices(X0,X1,X1)
      | ~ sP9(X0) ) ),
    inference(general_splitting,[],[f76,f85_D])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_lattices(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => r3_lattices(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_lattices)).

fof(f577,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k8_filter_1(sK0))
      | sP9(sK0) ) ),
    inference(resolution,[],[f200,f85])).

fof(f101,plain,(
    v9_lattices(sK0) ),
    inference(global_subsumption,[],[f46,f45,f89])).

fof(f89,plain,
    ( ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v9_lattices(sK0) ),
    inference(resolution,[],[f44,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f1])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f100,plain,(
    v8_lattices(sK0) ),
    inference(global_subsumption,[],[f46,f45,f88])).

fof(f88,plain,
    ( ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v8_lattices(sK0) ),
    inference(resolution,[],[f44,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f99,plain,(
    v6_lattices(sK0) ),
    inference(global_subsumption,[],[f46,f45,f87])).

fof(f87,plain,
    ( ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v6_lattices(sK0) ),
    inference(resolution,[],[f44,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1448,plain,
    ( r2_hidden(sK3(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f1447])).

fof(f3057,plain,(
    spl10_31 ),
    inference(avatar_split_clause,[],[f102,f3046])).

fof(f3046,plain,
    ( spl10_31
  <=> v1_relat_1(k8_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f102,plain,(
    v1_relat_1(k8_filter_1(sK0)) ),
    inference(global_subsumption,[],[f46,f45,f91])).

fof(f91,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v1_relat_1(k8_filter_1(sK0)) ),
    inference(resolution,[],[f44,f58])).

fof(f58,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v1_relat_1(k8_filter_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(k8_filter_1(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(k8_filter_1(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => v1_relat_1(k8_filter_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_filter_1)).

fof(f3053,plain,
    ( ~ spl10_31
    | spl10_32
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f2964,f164,f3050,f3046])).

fof(f2964,plain,
    ( k3_relat_1(k8_filter_1(sK0)) = k2_xboole_0(k1_relat_1(k8_filter_1(sK0)),u1_struct_0(sK0))
    | ~ v1_relat_1(k8_filter_1(sK0))
    | ~ spl10_2 ),
    inference(superposition,[],[f48,f165])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f2885,plain,
    ( ~ spl10_16
    | spl10_30
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f1932,f1420,f2883,f1430])).

fof(f1420,plain,
    ( spl10_14
  <=> ! [X0] : ~ r2_hidden(k4_tarski(X0,sK6(k8_filter_1(sK0),u1_struct_0(sK0))),k8_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f1932,plain,
    ( ! [X1] :
        ( ~ r3_lattices(sK0,X1,sK6(k8_filter_1(sK0),u1_struct_0(sK0)))
        | ~ m1_subset_1(sK6(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl10_14 ),
    inference(resolution,[],[f1421,f1013])).

fof(f1013,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(X2,X3),k8_filter_1(sK0))
      | ~ r3_lattices(sK0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f174,f1011])).

fof(f1011,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(X2,X3),k8_filter_1(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f1010])).

fof(f1010,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(X2,X3),k8_filter_1(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f905,f79])).

fof(f905,plain,(
    ! [X4,X5] :
      ( r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),X4,X5),k8_filter_1(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f108,f103])).

fof(f108,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),X4,X5),a_1_0_filter_1(sK0)) ) ),
    inference(global_subsumption,[],[f46,f45,f97])).

fof(f97,plain,(
    ! [X4,X5] :
      ( ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X4,X5)
      | r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),X4,X5),a_1_0_filter_1(sK0)) ) ),
    inference(resolution,[],[f44,f80])).

fof(f1421,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK6(k8_filter_1(sK0),u1_struct_0(sK0))),k8_filter_1(sK0))
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f1420])).

fof(f1987,plain,
    ( spl10_17
    | spl10_29
    | spl10_3 ),
    inference(avatar_split_clause,[],[f1090,f168,f1984,f1447])).

fof(f1090,plain,
    ( r2_hidden(k4_tarski(sK3(k8_filter_1(sK0),u1_struct_0(sK0)),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),k8_filter_1(sK0))
    | r2_hidden(sK3(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | spl10_3 ),
    inference(equality_resolution,[],[f191])).

fof(f191,plain,
    ( ! [X0] :
        ( u1_struct_0(sK0) != X0
        | r2_hidden(k4_tarski(sK3(k8_filter_1(sK0),X0),sK5(k8_filter_1(sK0),X0)),k8_filter_1(sK0))
        | r2_hidden(sK3(k8_filter_1(sK0),X0),X0) )
    | spl10_3 ),
    inference(superposition,[],[f170,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK5(X0,X1)),X0)
      | r2_hidden(sK3(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f170,plain,
    ( u1_struct_0(sK0) != k1_relat_1(k8_filter_1(sK0))
    | spl10_3 ),
    inference(avatar_component_clause,[],[f168])).

fof(f1919,plain,
    ( ~ spl10_13
    | spl10_16 ),
    inference(avatar_contradiction_clause,[],[f1917])).

fof(f1917,plain,
    ( $false
    | ~ spl10_13
    | spl10_16 ),
    inference(subsumption_resolution,[],[f1432,f1916])).

fof(f1916,plain,
    ( m1_subset_1(sK6(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl10_13 ),
    inference(resolution,[],[f1417,f61])).

fof(f1432,plain,
    ( ~ m1_subset_1(sK6(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | spl10_16 ),
    inference(avatar_component_clause,[],[f1430])).

fof(f1913,plain,
    ( spl10_13
    | spl10_28
    | spl10_2 ),
    inference(avatar_split_clause,[],[f1074,f164,f1910,f1416])).

fof(f1074,plain,
    ( r2_hidden(k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK6(k8_filter_1(sK0),u1_struct_0(sK0))),k8_filter_1(sK0))
    | r2_hidden(sK6(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | spl10_2 ),
    inference(equality_resolution,[],[f176])).

fof(f176,plain,
    ( ! [X0] :
        ( u1_struct_0(sK0) != X0
        | r2_hidden(k4_tarski(sK8(k8_filter_1(sK0),X0),sK6(k8_filter_1(sK0),X0)),k8_filter_1(sK0))
        | r2_hidden(sK6(k8_filter_1(sK0),X0),X0) )
    | spl10_2 ),
    inference(superposition,[],[f166,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1),sK6(X0,X1)),X0)
      | r2_hidden(sK6(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f166,plain,
    ( u1_struct_0(sK0) != k2_relat_1(k8_filter_1(sK0))
    | spl10_2 ),
    inference(avatar_component_clause,[],[f164])).

fof(f1453,plain,
    ( ~ spl10_17
    | spl10_18
    | spl10_3 ),
    inference(avatar_split_clause,[],[f900,f168,f1451,f1447])).

fof(f900,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK3(k8_filter_1(sK0),u1_struct_0(sK0)),X0),k8_filter_1(sK0))
        | ~ r2_hidden(sK3(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) )
    | spl10_3 ),
    inference(equality_resolution,[],[f192])).

fof(f192,plain,
    ( ! [X2,X1] :
        ( u1_struct_0(sK0) != X1
        | ~ r2_hidden(k4_tarski(sK3(k8_filter_1(sK0),X1),X2),k8_filter_1(sK0))
        | ~ r2_hidden(sK3(k8_filter_1(sK0),X1),X1) )
    | spl10_3 ),
    inference(superposition,[],[f170,f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
      | ~ r2_hidden(sK3(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f1422,plain,
    ( ~ spl10_13
    | spl10_14
    | spl10_2 ),
    inference(avatar_split_clause,[],[f862,f164,f1420,f1416])).

fof(f862,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK6(k8_filter_1(sK0),u1_struct_0(sK0))),k8_filter_1(sK0))
        | ~ r2_hidden(sK6(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) )
    | spl10_2 ),
    inference(equality_resolution,[],[f177])).

fof(f177,plain,
    ( ! [X2,X1] :
        ( u1_struct_0(sK0) != X1
        | ~ r2_hidden(k4_tarski(X2,sK6(k8_filter_1(sK0),X1)),k8_filter_1(sK0))
        | ~ r2_hidden(sK6(k8_filter_1(sK0),X1),X1) )
    | spl10_2 ),
    inference(superposition,[],[f166,f75])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
      | ~ r2_hidden(sK6(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f209,plain,
    ( ~ spl10_4
    | spl10_5 ),
    inference(avatar_split_clause,[],[f109,f207,f203])).

fof(f109,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ sP9(sK0)
      | r3_lattices(sK0,X6,X6) ) ),
    inference(global_subsumption,[],[f46,f99,f100,f101,f98])).

fof(f98,plain,(
    ! [X6] :
      ( ~ v6_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | r3_lattices(sK0,X6,X6)
      | ~ sP9(sK0) ) ),
    inference(resolution,[],[f44,f86])).

fof(f171,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f43,f168,f164,f160])).

fof(f43,plain,
    ( u1_struct_0(sK0) != k1_relat_1(k8_filter_1(sK0))
    | u1_struct_0(sK0) != k2_relat_1(k8_filter_1(sK0))
    | u1_struct_0(sK0) != k3_relat_1(k8_filter_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

%------------------------------------------------------------------------------
