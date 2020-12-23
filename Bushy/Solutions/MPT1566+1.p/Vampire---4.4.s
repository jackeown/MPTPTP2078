%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t44_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:42 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 124 expanded)
%              Number of leaves         :   15 (  42 expanded)
%              Depth                    :   15
%              Number of atoms          :  298 ( 474 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f256,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f79,f83,f87,f98,f102,f109,f113,f153,f245])).

fof(f245,plain,
    ( ~ spl5_2
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_12
    | spl5_15
    | ~ spl5_20 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_15
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f243,f112])).

fof(f112,plain,
    ( ~ r1_orders_2(sK0,k3_yellow_0(sK0),sK1)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl5_15
  <=> ~ r1_orders_2(sK0,k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f243,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK1)
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_20 ),
    inference(forward_demodulation,[],[f242,f152])).

fof(f152,plain,
    ( k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl5_20
  <=> k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f242,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),sK1)
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f241,f97])).

fof(f97,plain,
    ( r1_yellow_0(sK0,k1_xboole_0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl5_8
  <=> r1_yellow_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f241,plain,
    ( ~ r1_yellow_0(sK0,k1_xboole_0)
    | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),sK1)
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f238,f101])).

fof(f101,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl5_10
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f238,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,k1_xboole_0)
    | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),sK1)
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_12 ),
    inference(resolution,[],[f142,f108])).

fof(f108,plain,
    ( r2_lattice3(sK0,k1_xboole_0,sK1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl5_12
  <=> r2_lattice3(sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,X0)
        | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) )
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f141,f78])).

fof(f78,plain,
    ( v5_orders_2(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl5_2
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f141,plain,
    ( ! [X0,X1] :
        ( ~ v5_orders_2(sK0)
        | ~ r1_yellow_0(sK0,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) )
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f137,f86])).

fof(f86,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl5_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f137,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ r1_yellow_0(sK0,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) )
    | ~ spl5_6 ),
    inference(resolution,[],[f89,f71])).

fof(f71,plain,(
    ! [X4,X2,X0] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X4)
      | r1_orders_2(X0,k1_yellow_0(X0,X2),X4) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k1_yellow_0(X0,X2) != X1
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X4)
      | r1_orders_2(X0,X1,X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X1,X4) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t44_yellow_0.p',t30_yellow_0)).

fof(f89,plain,
    ( ! [X0] : m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))
    | ~ spl5_6 ),
    inference(resolution,[],[f86,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t44_yellow_0.p',dt_k1_yellow_0)).

fof(f153,plain,
    ( spl5_20
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f91,f85,f151])).

fof(f91,plain,
    ( k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)
    | ~ spl5_6 ),
    inference(resolution,[],[f86,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t44_yellow_0.p',d11_yellow_0)).

fof(f113,plain,(
    ~ spl5_15 ),
    inference(avatar_split_clause,[],[f44,f111])).

fof(f44,plain,(
    ~ r1_orders_2(sK0,k3_yellow_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_orders_2(X0,k3_yellow_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_orders_2(X0,k3_yellow_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t44_yellow_0.p',t44_yellow_0)).

fof(f109,plain,
    ( spl5_12
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f105,f100,f85,f107])).

fof(f105,plain,
    ( r2_lattice3(sK0,k1_xboole_0,sK1)
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f103,f86])).

fof(f103,plain,
    ( ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,k1_xboole_0,sK1)
    | ~ spl5_10 ),
    inference(resolution,[],[f101,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,k1_xboole_0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_lattice3(X0,k1_xboole_0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_lattice3(X0,k1_xboole_0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t44_yellow_0.p',t6_yellow_0)).

fof(f102,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f43,f100])).

fof(f43,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f98,plain,
    ( spl5_8
    | spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f94,f85,f81,f77,f73,f96])).

fof(f73,plain,
    ( spl5_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f81,plain,
    ( spl5_4
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f94,plain,
    ( r1_yellow_0(sK0,k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f93,f74])).

fof(f74,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f93,plain,
    ( v2_struct_0(sK0)
    | r1_yellow_0(sK0,k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f92,f82])).

fof(f82,plain,
    ( v1_yellow_0(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f92,plain,
    ( ~ v1_yellow_0(sK0)
    | v2_struct_0(sK0)
    | r1_yellow_0(sK0,k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f88,f78])).

fof(f88,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v1_yellow_0(sK0)
    | v2_struct_0(sK0)
    | r1_yellow_0(sK0,k1_xboole_0)
    | ~ spl5_6 ),
    inference(resolution,[],[f86,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | v2_struct_0(X0)
      | r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t44_yellow_0.p',t42_yellow_0)).

fof(f87,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f48,f85])).

fof(f48,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f83,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f47,f81])).

fof(f47,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f79,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f46,f77])).

fof(f46,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f45,f73])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
