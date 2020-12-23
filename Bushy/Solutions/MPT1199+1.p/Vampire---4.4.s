%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : lattices__t26_lattices.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:01 EDT 2019

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 188 expanded)
%              Number of leaves         :   15 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :  380 ( 778 expanded)
%              Number of equality atoms :   54 (  95 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f245,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f82,f86,f90,f94,f98,f102,f106,f158,f162,f229,f244])).

fof(f244,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | spl5_7
    | ~ spl5_8
    | ~ spl5_14
    | ~ spl5_16
    | ~ spl5_30 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_14
    | ~ spl5_16
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f242,f89])).

fof(f89,plain,
    ( sK1 != sK2
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl5_7
  <=> sK1 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f242,plain,
    ( sK1 = sK2
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_14
    | ~ spl5_16
    | ~ spl5_30 ),
    inference(forward_demodulation,[],[f241,f235])).

fof(f235,plain,
    ( k3_lattices(sK0,sK1,sK2) = sK1
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_14
    | ~ spl5_30 ),
    inference(forward_demodulation,[],[f231,f228])).

fof(f228,plain,
    ( k3_lattices(sK0,sK2,sK1) = sK1
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl5_30
  <=> k3_lattices(sK0,sK2,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f231,plain,
    ( k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(resolution,[],[f123,f105])).

fof(f105,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_14
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f123,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k3_lattices(sK0,X3,sK2) = k3_lattices(sK0,sK2,X3) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f122,f77])).

fof(f77,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl5_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f122,plain,
    ( ! [X3] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k3_lattices(sK0,X3,sK2) = k3_lattices(sK0,sK2,X3) )
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f121,f85])).

fof(f85,plain,
    ( l2_lattices(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl5_4
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f121,plain,
    ( ! [X3] :
        ( ~ l2_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k3_lattices(sK0,X3,sK2) = k3_lattices(sK0,sK2,X3) )
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f110,f81])).

fof(f81,plain,
    ( v4_lattices(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl5_2
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f110,plain,
    ( ! [X3] :
        ( ~ v4_lattices(sK0)
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k3_lattices(sK0,X3,sK2) = k3_lattices(sK0,sK2,X3) )
    | ~ spl5_8 ),
    inference(resolution,[],[f93,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t26_lattices.p',commutativity_k3_lattices)).

fof(f93,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl5_8
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f241,plain,
    ( k3_lattices(sK0,sK1,sK2) = sK2
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f238,f157])).

fof(f157,plain,
    ( k1_lattices(sK0,sK1,sK2) = sK2
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl5_16
  <=> k1_lattices(sK0,sK1,sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f238,plain,
    ( k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK2)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(resolution,[],[f149,f93])).

fof(f149,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k3_lattices(sK0,sK1,X2) = k1_lattices(sK0,sK1,X2) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f148,f77])).

fof(f148,plain,
    ( ! [X2] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k3_lattices(sK0,sK1,X2) = k1_lattices(sK0,sK1,X2) )
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f147,f85])).

fof(f147,plain,
    ( ! [X2] :
        ( ~ l2_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k3_lattices(sK0,sK1,X2) = k1_lattices(sK0,sK1,X2) )
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f138,f81])).

fof(f138,plain,
    ( ! [X2] :
        ( ~ v4_lattices(sK0)
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k3_lattices(sK0,sK1,X2) = k1_lattices(sK0,sK1,X2) )
    | ~ spl5_14 ),
    inference(resolution,[],[f105,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t26_lattices.p',redefinition_k3_lattices)).

fof(f229,plain,
    ( spl5_30
    | spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_14
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f225,f160,f104,f92,f84,f80,f76,f227])).

fof(f160,plain,
    ( spl5_18
  <=> k1_lattices(sK0,sK2,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f225,plain,
    ( k3_lattices(sK0,sK2,sK1) = sK1
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_14
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f222,f161])).

fof(f161,plain,
    ( k1_lattices(sK0,sK2,sK1) = sK1
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f160])).

fof(f222,plain,
    ( k3_lattices(sK0,sK2,sK1) = k1_lattices(sK0,sK2,sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(resolution,[],[f120,f105])).

fof(f120,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k3_lattices(sK0,sK2,X2) = k1_lattices(sK0,sK2,X2) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f119,f77])).

fof(f119,plain,
    ( ! [X2] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k3_lattices(sK0,sK2,X2) = k1_lattices(sK0,sK2,X2) )
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f118,f85])).

fof(f118,plain,
    ( ! [X2] :
        ( ~ l2_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k3_lattices(sK0,sK2,X2) = k1_lattices(sK0,sK2,X2) )
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f109,f81])).

fof(f109,plain,
    ( ! [X2] :
        ( ~ v4_lattices(sK0)
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k3_lattices(sK0,sK2,X2) = k1_lattices(sK0,sK2,X2) )
    | ~ spl5_8 ),
    inference(resolution,[],[f93,f66])).

fof(f162,plain,
    ( spl5_18
    | spl5_1
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f135,f104,f100,f92,f84,f76,f160])).

fof(f100,plain,
    ( spl5_12
  <=> r1_lattices(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f135,plain,
    ( k1_lattices(sK0,sK2,sK1) = sK1
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f134,f77])).

fof(f134,plain,
    ( k1_lattices(sK0,sK2,sK1) = sK1
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f133,f105])).

fof(f133,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k1_lattices(sK0,sK2,sK1) = sK1
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f132,f93])).

fof(f132,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k1_lattices(sK0,sK2,sK1) = sK1
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f131,f85])).

fof(f131,plain,
    ( ~ l2_lattices(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k1_lattices(sK0,sK2,sK1) = sK1
    | v2_struct_0(sK0)
    | ~ spl5_12 ),
    inference(resolution,[],[f101,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) = X2
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t26_lattices.p',d3_lattices)).

fof(f101,plain,
    ( r1_lattices(sK0,sK2,sK1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f100])).

fof(f158,plain,
    ( spl5_16
    | spl5_1
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f130,f104,f96,f92,f84,f76,f156])).

fof(f96,plain,
    ( spl5_10
  <=> r1_lattices(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f130,plain,
    ( k1_lattices(sK0,sK1,sK2) = sK2
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f129,f77])).

fof(f129,plain,
    ( k1_lattices(sK0,sK1,sK2) = sK2
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f128,f93])).

fof(f128,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | k1_lattices(sK0,sK1,sK2) = sK2
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f127,f105])).

fof(f127,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | k1_lattices(sK0,sK1,sK2) = sK2
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f126,f85])).

fof(f126,plain,
    ( ~ l2_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | k1_lattices(sK0,sK1,sK2) = sK2
    | v2_struct_0(sK0)
    | ~ spl5_10 ),
    inference(resolution,[],[f97,f62])).

fof(f97,plain,
    ( r1_lattices(sK0,sK1,sK2)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f96])).

fof(f106,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f56,f104])).

fof(f56,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_lattices(X0,X2,X1)
              & r1_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l2_lattices(X0)
      & v4_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_lattices(X0,X2,X1)
              & r1_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l2_lattices(X0)
      & v4_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l2_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ( r1_lattices(X0,X2,X1)
                    & r1_lattices(X0,X1,X2) )
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_lattices(X0,X2,X1)
                  & r1_lattices(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t26_lattices.p',t26_lattices)).

fof(f102,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f54,f100])).

fof(f54,plain,(
    r1_lattices(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f98,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f53,f96])).

fof(f53,plain,(
    r1_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f94,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f52,f92])).

fof(f52,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f90,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f55,f88])).

fof(f55,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f86,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f59,f84])).

fof(f59,plain,(
    l2_lattices(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f82,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f58,f80])).

fof(f58,plain,(
    v4_lattices(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f78,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f57,f76])).

fof(f57,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
