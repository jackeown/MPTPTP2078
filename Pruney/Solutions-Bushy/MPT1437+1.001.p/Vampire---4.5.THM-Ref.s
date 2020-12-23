%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1437+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:55 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 384 expanded)
%              Number of leaves         :   32 ( 151 expanded)
%              Depth                    :   18
%              Number of atoms          :  698 (1857 expanded)
%              Number of equality atoms :   68 ( 154 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f810,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f78,f88,f90,f97,f111,f118,f134,f149,f189,f253,f318,f549,f611,f685,f767,f808,f809])).

fof(f809,plain,
    ( sK1 != sK3(k4_tarski(sK1,sK2),sK0)
    | sK2 != sK4(k4_tarski(sK1,sK2),sK0)
    | ~ r3_lattices(sK0,sK3(k4_tarski(sK1,sK2),sK0),sK2)
    | r3_lattices(sK0,sK1,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f808,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_9
    | ~ spl5_18
    | spl5_35
    | ~ spl5_51 ),
    inference(avatar_contradiction_clause,[],[f807])).

fof(f807,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_9
    | ~ spl5_18
    | spl5_35
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f806,f252])).

fof(f252,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),k8_filter_1(sK0))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl5_18
  <=> r2_hidden(k4_tarski(sK1,sK2),k8_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f806,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),k8_filter_1(sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_9
    | spl5_35
    | ~ spl5_51 ),
    inference(forward_demodulation,[],[f805,f117])).

fof(f117,plain,
    ( k8_filter_1(sK0) = a_1_0_filter_1(sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl5_9
  <=> k8_filter_1(sK0) = a_1_0_filter_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f805,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),a_1_0_filter_1(sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_35
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f804,f57])).

fof(f57,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f804,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),a_1_0_filter_1(sK0))
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | spl5_35
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f803,f62])).

fof(f62,plain,
    ( v10_lattices(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl5_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f803,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),a_1_0_filter_1(sK0))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3
    | spl5_35
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f802,f67])).

fof(f67,plain,
    ( l3_lattices(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl5_3
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f802,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),a_1_0_filter_1(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl5_35
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f789,f473])).

fof(f473,plain,
    ( ~ r3_lattices(sK0,sK3(k4_tarski(sK1,sK2),sK0),sK2)
    | spl5_35 ),
    inference(avatar_component_clause,[],[f471])).

fof(f471,plain,
    ( spl5_35
  <=> r3_lattices(sK0,sK3(k4_tarski(sK1,sK2),sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f789,plain,
    ( r3_lattices(sK0,sK3(k4_tarski(sK1,sK2),sK0),sK2)
    | ~ r2_hidden(k4_tarski(sK1,sK2),a_1_0_filter_1(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_51 ),
    inference(superposition,[],[f48,f684])).

fof(f684,plain,
    ( sK2 = sK4(k4_tarski(sK1,sK2),sK0)
    | ~ spl5_51 ),
    inference(avatar_component_clause,[],[f682])).

fof(f682,plain,
    ( spl5_51
  <=> sK2 = sK4(k4_tarski(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r3_lattices(X1,sK3(X0,X1),sK4(X0,X1))
      | ~ r2_hidden(X0,a_1_0_filter_1(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,a_1_0_filter_1(X1))
          | ! [X2,X3] :
              ( ~ r3_lattices(X1,X2,X3)
              | k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) != X0
              | ~ m1_subset_1(X3,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
        & ( ( r3_lattices(X1,sK3(X0,X1),sK4(X0,X1))
            & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),sK3(X0,X1),sK4(X0,X1)) = X0
            & m1_subset_1(sK4(X0,X1),u1_struct_0(X1))
            & m1_subset_1(sK3(X0,X1),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_1_0_filter_1(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X4,X5] :
          ( r3_lattices(X1,X4,X5)
          & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X4,X5) = X0
          & m1_subset_1(X5,u1_struct_0(X1))
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattices(X1,sK3(X0,X1),sK4(X0,X1))
        & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),sK3(X0,X1),sK4(X0,X1)) = X0
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X1))
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,a_1_0_filter_1(X1))
          | ! [X2,X3] :
              ( ~ r3_lattices(X1,X2,X3)
              | k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) != X0
              | ~ m1_subset_1(X3,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
        & ( ? [X4,X5] :
              ( r3_lattices(X1,X4,X5)
              & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X4,X5) = X0
              & m1_subset_1(X5,u1_struct_0(X1))
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_1_0_filter_1(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,a_1_0_filter_1(X1))
          | ! [X2,X3] :
              ( ~ r3_lattices(X1,X2,X3)
              | k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) != X0
              | ~ m1_subset_1(X3,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
        & ( ? [X2,X3] :
              ( r3_lattices(X1,X2,X3)
              & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) = X0
              & m1_subset_1(X3,u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_1_0_filter_1(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f767,plain,
    ( spl5_59
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f636,f608,f764])).

fof(f764,plain,
    ( spl5_59
  <=> sK1 = sK3(k4_tarski(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f608,plain,
    ( spl5_44
  <=> k4_tarski(sK1,sK2) = k4_tarski(sK3(k4_tarski(sK1,sK2),sK0),sK4(k4_tarski(sK1,sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f636,plain,
    ( sK1 = sK3(k4_tarski(sK1,sK2),sK0)
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f610,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X2,X3) != k4_tarski(X0,X1)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k4_tarski(X2,X3) != k4_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X2,X3) = k4_tarski(X0,X1)
     => ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_zfmisc_1)).

fof(f610,plain,
    ( k4_tarski(sK1,sK2) = k4_tarski(sK3(k4_tarski(sK1,sK2),sK0),sK4(k4_tarski(sK1,sK2),sK0))
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f608])).

fof(f685,plain,
    ( spl5_51
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f635,f608,f682])).

fof(f635,plain,
    ( sK2 = sK4(k4_tarski(sK1,sK2),sK0)
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f610,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X2,X3) != k4_tarski(X0,X1)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f611,plain,
    ( spl5_44
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_9
    | spl5_10
    | ~ spl5_14
    | ~ spl5_25
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f578,f527,f315,f186,f128,f115,f81,f65,f60,f55,f608])).

fof(f81,plain,
    ( spl5_6
  <=> r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f128,plain,
    ( spl5_10
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f186,plain,
    ( spl5_14
  <=> k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2) = k4_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f315,plain,
    ( spl5_25
  <=> k4_tarski(sK1,sK2) = k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK3(k4_tarski(sK1,sK2),sK0),sK4(k4_tarski(sK1,sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f527,plain,
    ( spl5_39
  <=> m1_subset_1(sK4(k4_tarski(sK1,sK2),sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f578,plain,
    ( k4_tarski(sK1,sK2) = k4_tarski(sK3(k4_tarski(sK1,sK2),sK0),sK4(k4_tarski(sK1,sK2),sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_9
    | spl5_10
    | ~ spl5_14
    | ~ spl5_25
    | ~ spl5_39 ),
    inference(forward_demodulation,[],[f569,f317])).

fof(f317,plain,
    ( k4_tarski(sK1,sK2) = k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK3(k4_tarski(sK1,sK2),sK0),sK4(k4_tarski(sK1,sK2),sK0))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f315])).

fof(f569,plain,
    ( k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK3(k4_tarski(sK1,sK2),sK0),sK4(k4_tarski(sK1,sK2),sK0)) = k4_tarski(sK3(k4_tarski(sK1,sK2),sK0),sK4(k4_tarski(sK1,sK2),sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_9
    | spl5_10
    | ~ spl5_14
    | ~ spl5_39 ),
    inference(unit_resulting_resolution,[],[f129,f528,f242])).

fof(f242,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0)
        | k1_domain_1(u1_struct_0(sK0),X0,sK3(k4_tarski(sK1,sK2),sK0),X1) = k4_tarski(sK3(k4_tarski(sK1,sK2),sK0),X1) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f239,f188])).

fof(f188,plain,
    ( k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2) = k4_tarski(sK1,sK2)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f186])).

fof(f239,plain,
    ( ! [X0,X1] :
        ( k1_domain_1(u1_struct_0(sK0),X0,sK3(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),sK0),X1) = k4_tarski(sK3(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),sK0),X1)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(resolution,[],[f176,f83])).

fof(f83,plain,
    ( r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f176,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X1,k8_filter_1(sK0))
        | k1_domain_1(u1_struct_0(sK0),X0,sK3(X1,sK0),X2) = k4_tarski(sK3(X1,sK0),X2)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X2,X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f175,f117])).

fof(f175,plain,
    ( ! [X2,X0,X1] :
        ( k1_domain_1(u1_struct_0(sK0),X0,sK3(X1,sK0),X2) = k4_tarski(sK3(X1,sK0),X2)
        | v1_xboole_0(X0)
        | ~ r2_hidden(X1,a_1_0_filter_1(sK0))
        | ~ m1_subset_1(X2,X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f174,f57])).

fof(f174,plain,
    ( ! [X2,X0,X1] :
        ( k1_domain_1(u1_struct_0(sK0),X0,sK3(X1,sK0),X2) = k4_tarski(sK3(X1,sK0),X2)
        | v1_xboole_0(X0)
        | ~ r2_hidden(X1,a_1_0_filter_1(sK0))
        | ~ m1_subset_1(X2,X0)
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f173,f62])).

fof(f173,plain,
    ( ! [X2,X0,X1] :
        ( k1_domain_1(u1_struct_0(sK0),X0,sK3(X1,sK0),X2) = k4_tarski(sK3(X1,sK0),X2)
        | v1_xboole_0(X0)
        | ~ r2_hidden(X1,a_1_0_filter_1(sK0))
        | ~ m1_subset_1(X2,X0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f104,f67])).

fof(f104,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ l3_lattices(X6)
      | k1_domain_1(u1_struct_0(X6),X5,sK3(X7,X6),X4) = k4_tarski(sK3(X7,X6),X4)
      | v1_xboole_0(X5)
      | ~ r2_hidden(X7,a_1_0_filter_1(X6))
      | ~ m1_subset_1(X4,X5)
      | ~ v10_lattices(X6)
      | v2_struct_0(X6) ) ),
    inference(global_subsumption,[],[f41,f42,f43,f102])).

fof(f102,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(X4,X5)
      | k1_domain_1(u1_struct_0(X6),X5,sK3(X7,X6),X4) = k4_tarski(sK3(X7,X6),X4)
      | v1_xboole_0(X5)
      | v1_xboole_0(u1_struct_0(X6))
      | ~ r2_hidden(X7,a_1_0_filter_1(X6))
      | ~ l3_lattices(X6)
      | ~ v10_lattices(X6)
      | v2_struct_0(X6) ) ),
    inference(resolution,[],[f52,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_1_0_filter_1(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X3,X1)
      | k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X1)
        & m1_subset_1(X2,X0)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_domain_1)).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f42,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f41,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_lattices(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_lattices)).

fof(f528,plain,
    ( m1_subset_1(sK4(k4_tarski(sK1,sK2),sK0),u1_struct_0(sK0))
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f527])).

fof(f129,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f549,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_9
    | ~ spl5_18
    | spl5_39 ),
    inference(avatar_contradiction_clause,[],[f548])).

fof(f548,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_9
    | ~ spl5_18
    | spl5_39 ),
    inference(subsumption_resolution,[],[f547,f252])).

fof(f547,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),k8_filter_1(sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_9
    | spl5_39 ),
    inference(forward_demodulation,[],[f546,f117])).

fof(f546,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),a_1_0_filter_1(sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_39 ),
    inference(subsumption_resolution,[],[f545,f57])).

fof(f545,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),a_1_0_filter_1(sK0))
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | spl5_39 ),
    inference(subsumption_resolution,[],[f544,f62])).

fof(f544,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),a_1_0_filter_1(sK0))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3
    | spl5_39 ),
    inference(subsumption_resolution,[],[f540,f67])).

fof(f540,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),a_1_0_filter_1(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl5_39 ),
    inference(resolution,[],[f529,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_1_0_filter_1(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f529,plain,
    ( ~ m1_subset_1(sK4(k4_tarski(sK1,sK2),sK0),u1_struct_0(sK0))
    | spl5_39 ),
    inference(avatar_component_clause,[],[f527])).

fof(f318,plain,
    ( spl5_25
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f230,f186,f115,f81,f65,f60,f55,f315])).

fof(f230,plain,
    ( k4_tarski(sK1,sK2) = k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK3(k4_tarski(sK1,sK2),sK0),sK4(k4_tarski(sK1,sK2),sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f228,f188])).

fof(f228,plain,
    ( k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2) = k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK3(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),sK0),sK4(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f83,f126])).

fof(f126,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k8_filter_1(sK0))
        | k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK3(X2,sK0),sK4(X2,sK0)) = X2 )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f125,f57])).

fof(f125,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k8_filter_1(sK0))
        | k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK3(X2,sK0),sK4(X2,sK0)) = X2
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f124,f62])).

fof(f124,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k8_filter_1(sK0))
        | k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK3(X2,sK0),sK4(X2,sK0)) = X2
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f120,f67])).

fof(f120,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k8_filter_1(sK0))
        | k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK3(X2,sK0),sK4(X2,sK0)) = X2
        | ~ l3_lattices(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_9 ),
    inference(superposition,[],[f47,f117])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_1_0_filter_1(X1))
      | k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),sK3(X0,X1),sK4(X0,X1)) = X0
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f253,plain,
    ( spl5_18
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f205,f186,f81,f250])).

fof(f205,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),k8_filter_1(sK0))
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(superposition,[],[f83,f188])).

fof(f189,plain,
    ( spl5_14
    | ~ spl5_5
    | spl5_10
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f150,f132,f128,f75,f186])).

fof(f75,plain,
    ( spl5_5
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f132,plain,
    ( spl5_11
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | k1_domain_1(u1_struct_0(sK0),X1,sK1,X0) = k4_tarski(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f150,plain,
    ( k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2) = k4_tarski(sK1,sK2)
    | ~ spl5_5
    | spl5_10
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f136,f129])).

fof(f136,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2) = k4_tarski(sK1,sK2)
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(resolution,[],[f133,f77])).

fof(f77,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | k1_domain_1(u1_struct_0(sK0),X1,sK1,X0) = k4_tarski(sK1,X0) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f149,plain,
    ( spl5_1
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl5_1
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f147,f57])).

fof(f147,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f144,f113])).

fof(f113,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f96,f41])).

fof(f96,plain,
    ( l1_lattices(sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl5_8
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f144,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_10 ),
    inference(resolution,[],[f130,f43])).

fof(f130,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f134,plain,
    ( spl5_10
    | spl5_11
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f100,f70,f132,f128])).

fof(f70,plain,
    ( spl5_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,X1)
        | k1_domain_1(u1_struct_0(sK0),X1,sK1,X0) = k4_tarski(sK1,X0)
        | v1_xboole_0(X1)
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f52,f72])).

fof(f72,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f118,plain,
    ( spl5_9
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f98,f65,f60,f55,f115])).

fof(f98,plain,
    ( k8_filter_1(sK0) = a_1_0_filter_1(sK0)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f57,f62,f67,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | k8_filter_1(X0) = a_1_0_filter_1(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k8_filter_1(X0) = a_1_0_filter_1(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k8_filter_1(X0) = a_1_0_filter_1(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k8_filter_1(X0) = a_1_0_filter_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_filter_1)).

fof(f111,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f109,f82])).

fof(f82,plain,
    ( ~ r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f109,plain,
    ( r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f106,f98])).

fof(f106,plain,
    ( r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),a_1_0_filter_1(sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f57,f62,f67,f72,f87,f77,f53])).

fof(f53,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3),a_1_0_filter_1(X1))
      | ~ r3_lattices(X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_1_0_filter_1(X1))
      | ~ r3_lattices(X1,X2,X3)
      | k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) != X0
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f87,plain,
    ( r3_lattices(sK0,sK1,sK2)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl5_7
  <=> r3_lattices(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f97,plain,
    ( spl5_8
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f79,f65,f94])).

fof(f79,plain,
    ( l1_lattices(sK0)
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f67,f42])).

fof(f90,plain,
    ( ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f89,f85,f81])).

fof(f89,plain,
    ( ~ r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0))
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f40,f87])).

fof(f40,plain,
    ( ~ r3_lattices(sK0,sK1,sK2)
    | ~ r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ r3_lattices(sK0,sK1,sK2)
      | ~ r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) )
    & ( r3_lattices(sK0,sK1,sK2)
      | r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r3_lattices(X0,X1,X2)
                  | ~ r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) )
                & ( r3_lattices(X0,X1,X2)
                  | r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(sK0,X1,X2)
                | ~ r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),X1,X2),k8_filter_1(sK0)) )
              & ( r3_lattices(sK0,X1,X2)
                | r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),X1,X2),k8_filter_1(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r3_lattices(sK0,X1,X2)
              | ~ r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),X1,X2),k8_filter_1(sK0)) )
            & ( r3_lattices(sK0,X1,X2)
              | r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),X1,X2),k8_filter_1(sK0)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ r3_lattices(sK0,sK1,X2)
            | ~ r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,X2),k8_filter_1(sK0)) )
          & ( r3_lattices(sK0,sK1,X2)
            | r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,X2),k8_filter_1(sK0)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ( ~ r3_lattices(sK0,sK1,X2)
          | ~ r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,X2),k8_filter_1(sK0)) )
        & ( r3_lattices(sK0,sK1,X2)
          | r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,X2),k8_filter_1(sK0)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r3_lattices(sK0,sK1,sK2)
        | ~ r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) )
      & ( r3_lattices(sK0,sK1,sK2)
        | r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,X1,X2)
                | ~ r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) )
              & ( r3_lattices(X0,X1,X2)
                | r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,X1,X2)
                | ~ r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) )
              & ( r3_lattices(X0,X1,X2)
                | r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
              <~> r3_lattices(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
              <~> r3_lattices(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
                <=> r3_lattices(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
              <=> r3_lattices(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_filter_1)).

fof(f88,plain,
    ( spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f39,f85,f81])).

fof(f39,plain,
    ( r3_lattices(sK0,sK1,sK2)
    | r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f38,f75])).

fof(f38,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f37,f70])).

fof(f37,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f36,f65])).

fof(f36,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f35,f60])).

fof(f35,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f34,f55])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

%------------------------------------------------------------------------------
