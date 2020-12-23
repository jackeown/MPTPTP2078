%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 221 expanded)
%              Number of leaves         :   32 (  93 expanded)
%              Depth                    :   15
%              Number of atoms          :  458 ( 881 expanded)
%              Number of equality atoms :   27 (  85 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f365,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f78,f83,f88,f93,f98,f103,f108,f116,f129,f137,f169,f227,f242,f282,f356])).

fof(f356,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | spl7_18
    | ~ spl7_23 ),
    inference(avatar_contradiction_clause,[],[f355])).

fof(f355,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | spl7_18
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f354,f102])).

fof(f102,plain,
    ( ~ v2_struct_0(sK3)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl7_7
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f354,plain,
    ( v2_struct_0(sK3)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_18
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f353,f97])).

fof(f97,plain,
    ( v3_orders_2(sK3)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl7_6
  <=> v3_orders_2(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f353,plain,
    ( ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_18
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f352,f92])).

fof(f92,plain,
    ( v4_orders_2(sK3)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl7_5
  <=> v4_orders_2(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f352,plain,
    ( ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_18
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f351,f87])).

fof(f87,plain,
    ( v5_orders_2(sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl7_4
  <=> v5_orders_2(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f351,plain,
    ( ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ spl7_2
    | ~ spl7_3
    | spl7_18
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f350,f82])).

fof(f82,plain,
    ( l1_orders_2(sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl7_3
  <=> l1_orders_2(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f350,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ spl7_2
    | spl7_18
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f349,f281])).

fof(f281,plain,
    ( m1_subset_1(sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),u1_struct_0(sK3))
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl7_23
  <=> m1_subset_1(sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f349,plain,
    ( ~ m1_subset_1(sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ spl7_2
    | spl7_18 ),
    inference(subsumption_resolution,[],[f348,f77])).

fof(f77,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl7_2
  <=> m1_subset_1(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f348,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | spl7_18 ),
    inference(subsumption_resolution,[],[f327,f49])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f327,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | spl7_18 ),
    inference(resolution,[],[f57,f224])).

fof(f224,plain,
    ( ~ sP1(sK3,sK4,sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),k1_xboole_0)
    | spl7_18 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl7_18
  <=> sP1(sK3,sK4,sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X2,X1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( sP1(X0,X2,X1,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f17,f25,f24])).

fof(f24,plain,(
    ! [X3,X1,X2,X0] :
      ( sP0(X3,X1,X2,X0)
    <=> ( r2_hidden(X1,X3)
        & r2_orders_2(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

% (31462)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f25,plain,(
    ! [X0,X2,X1,X3] :
      ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
      <=> sP0(X3,X1,X2,X0) )
      | ~ sP1(X0,X2,X1,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

fof(f282,plain,
    ( spl7_23
    | ~ spl7_12
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f268,f239,f134,f279])).

fof(f134,plain,
    ( spl7_12
  <=> r2_hidden(sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),k3_orders_2(sK3,k1_xboole_0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f239,plain,
    ( spl7_19
  <=> m1_subset_1(k3_orders_2(sK3,k1_xboole_0,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f268,plain,
    ( m1_subset_1(sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),u1_struct_0(sK3))
    | ~ spl7_12
    | ~ spl7_19 ),
    inference(unit_resulting_resolution,[],[f136,f241,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f241,plain,
    ( m1_subset_1(k3_orders_2(sK3,k1_xboole_0,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f239])).

fof(f136,plain,
    ( r2_hidden(sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),k3_orders_2(sK3,k1_xboole_0,sK4))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f134])).

fof(f242,plain,
    ( spl7_19
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7 ),
    inference(avatar_split_clause,[],[f234,f100,f95,f90,f85,f80,f75,f239])).

fof(f234,plain,
    ( m1_subset_1(k3_orders_2(sK3,k1_xboole_0,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7 ),
    inference(unit_resulting_resolution,[],[f102,f97,f92,f87,f82,f77,f49,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

fof(f227,plain,
    ( ~ spl7_18
    | ~ spl7_12
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f226,f166,f134,f222])).

fof(f166,plain,
    ( spl7_15
  <=> sP6(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f226,plain,
    ( ~ sP1(sK3,sK4,sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),k1_xboole_0)
    | ~ spl7_12
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f218,f199])).

fof(f199,plain,
    ( ! [X2,X0,X1] : ~ sP0(k1_xboole_0,X0,X1,X2)
    | ~ spl7_15 ),
    inference(unit_resulting_resolution,[],[f183,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ~ r2_hidden(X1,X0)
        | ~ r2_orders_2(X3,X1,X2) )
      & ( ( r2_hidden(X1,X0)
          & r2_orders_2(X3,X1,X2) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X3,X1,X2,X0] :
      ( ( sP0(X3,X1,X2,X0)
        | ~ r2_hidden(X1,X3)
        | ~ r2_orders_2(X0,X1,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_orders_2(X0,X1,X2) )
        | ~ sP0(X3,X1,X2,X0) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X3,X1,X2,X0] :
      ( ( sP0(X3,X1,X2,X0)
        | ~ r2_hidden(X1,X3)
        | ~ r2_orders_2(X0,X1,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_orders_2(X0,X1,X2) )
        | ~ sP0(X3,X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f183,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl7_15 ),
    inference(unit_resulting_resolution,[],[f168,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP6(X1) ) ),
    inference(general_splitting,[],[f64,f67_D])).

fof(f67,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP6(X1) ) ),
    inference(cnf_transformation,[],[f67_D])).

fof(f67_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP6(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f168,plain,
    ( sP6(k1_xboole_0)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f166])).

fof(f218,plain,
    ( sP0(k1_xboole_0,sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),sK4,sK3)
    | ~ sP1(sK3,sK4,sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),k1_xboole_0)
    | ~ spl7_12 ),
    inference(resolution,[],[f52,f136])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,k3_orders_2(X0,X3,X1))
      | sP0(X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X2,k3_orders_2(X0,X3,X1))
          | ~ sP0(X3,X2,X1,X0) )
        & ( sP0(X3,X2,X1,X0)
          | ~ r2_hidden(X2,k3_orders_2(X0,X3,X1)) ) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X2,X1,X3] :
      ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
          | ~ sP0(X3,X1,X2,X0) )
        & ( sP0(X3,X1,X2,X0)
          | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
      | ~ sP1(X0,X2,X1,X3) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f169,plain,
    ( spl7_15
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f162,f105,f166])).

fof(f105,plain,
    ( spl7_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f162,plain,
    ( sP6(k1_xboole_0)
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f107,f49,f67])).

fof(f107,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f137,plain,
    ( spl7_12
    | spl7_11 ),
    inference(avatar_split_clause,[],[f131,f126,f134])).

fof(f126,plain,
    ( spl7_11
  <=> k1_xboole_0 = k3_orders_2(sK3,k1_xboole_0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

% (31462)Refutation not found, incomplete strategy% (31462)------------------------------
% (31462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f131,plain,
    ( r2_hidden(sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),k3_orders_2(sK3,k1_xboole_0,sK4))
    | spl7_11 ),
    inference(unit_resulting_resolution,[],[f128,f60])).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( sP2(sK5(X0),X0)
        & r2_hidden(sK5(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP2(X1,X0)
          & r2_hidden(X1,X0) )
     => ( sP2(sK5(X0),X0)
        & r2_hidden(sK5(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP2(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f18,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ! [X2,X3,X4,X5] :
          ( k4_mcart_1(X2,X3,X4,X5) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

% (31462)Termination reason: Refutation not found, incomplete strategy

% (31462)Memory used [KB]: 10618
% (31462)Time elapsed: 0.071 s
% (31462)------------------------------
% (31462)------------------------------
fof(f128,plain,
    ( k1_xboole_0 != k3_orders_2(sK3,k1_xboole_0,sK4)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f129,plain,
    ( ~ spl7_11
    | spl7_1
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f124,f112,f70,f126])).

fof(f70,plain,
    ( spl7_1
  <=> k1_xboole_0 = k3_orders_2(sK3,k1_struct_0(sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f112,plain,
    ( spl7_9
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f124,plain,
    ( k1_xboole_0 != k3_orders_2(sK3,k1_xboole_0,sK4)
    | spl7_1
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f118,f114])).

fof(f114,plain,
    ( l1_struct_0(sK3)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f112])).

fof(f118,plain,
    ( k1_xboole_0 != k3_orders_2(sK3,k1_xboole_0,sK4)
    | ~ l1_struct_0(sK3)
    | spl7_1 ),
    inference(superposition,[],[f72,f50])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

fof(f72,plain,
    ( k1_xboole_0 != k3_orders_2(sK3,k1_struct_0(sK3),sK4)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f116,plain,
    ( spl7_9
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f110,f80,f112])).

fof(f110,plain,
    ( l1_struct_0(sK3)
    | ~ spl7_3 ),
    inference(resolution,[],[f51,f82])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f108,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f48,f105])).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f103,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f41,f100])).

fof(f41,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k1_xboole_0 != k3_orders_2(sK3,k1_struct_0(sK3),sK4)
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f13,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 != k3_orders_2(sK3,k1_struct_0(sK3),X1)
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_orders_2(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( k1_xboole_0 != k3_orders_2(sK3,k1_struct_0(sK3),X1)
        & m1_subset_1(X1,u1_struct_0(sK3)) )
   => ( k1_xboole_0 != k3_orders_2(sK3,k1_struct_0(sK3),sK4)
      & m1_subset_1(sK4,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_orders_2)).

fof(f98,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f42,f95])).

fof(f42,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f93,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f43,f90])).

fof(f43,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f88,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f44,f85])).

fof(f44,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f83,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f45,f80])).

fof(f45,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f46,f75])).

fof(f46,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f47,f70])).

fof(f47,plain,(
    k1_xboole_0 != k3_orders_2(sK3,k1_struct_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:47:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (31446)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (31458)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.48  % (31448)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (31458)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f365,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f73,f78,f83,f88,f93,f98,f103,f108,f116,f129,f137,f169,f227,f242,f282,f356])).
% 0.20/0.49  fof(f356,plain,(
% 0.20/0.49    ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | spl7_18 | ~spl7_23),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f355])).
% 0.20/0.49  fof(f355,plain,(
% 0.20/0.49    $false | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | spl7_18 | ~spl7_23)),
% 0.20/0.49    inference(subsumption_resolution,[],[f354,f102])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    ~v2_struct_0(sK3) | spl7_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f100])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    spl7_7 <=> v2_struct_0(sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.49  fof(f354,plain,(
% 0.20/0.49    v2_struct_0(sK3) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | spl7_18 | ~spl7_23)),
% 0.20/0.49    inference(subsumption_resolution,[],[f353,f97])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    v3_orders_2(sK3) | ~spl7_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f95])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    spl7_6 <=> v3_orders_2(sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.49  fof(f353,plain,(
% 0.20/0.49    ~v3_orders_2(sK3) | v2_struct_0(sK3) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_18 | ~spl7_23)),
% 0.20/0.49    inference(subsumption_resolution,[],[f352,f92])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    v4_orders_2(sK3) | ~spl7_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f90])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    spl7_5 <=> v4_orders_2(sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.49  fof(f352,plain,(
% 0.20/0.49    ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | (~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_18 | ~spl7_23)),
% 0.20/0.49    inference(subsumption_resolution,[],[f351,f87])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    v5_orders_2(sK3) | ~spl7_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f85])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    spl7_4 <=> v5_orders_2(sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.49  fof(f351,plain,(
% 0.20/0.49    ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | (~spl7_2 | ~spl7_3 | spl7_18 | ~spl7_23)),
% 0.20/0.49    inference(subsumption_resolution,[],[f350,f82])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    l1_orders_2(sK3) | ~spl7_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f80])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    spl7_3 <=> l1_orders_2(sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.49  fof(f350,plain,(
% 0.20/0.49    ~l1_orders_2(sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | (~spl7_2 | spl7_18 | ~spl7_23)),
% 0.20/0.49    inference(subsumption_resolution,[],[f349,f281])).
% 0.20/0.49  fof(f281,plain,(
% 0.20/0.49    m1_subset_1(sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),u1_struct_0(sK3)) | ~spl7_23),
% 0.20/0.49    inference(avatar_component_clause,[],[f279])).
% 0.20/0.49  fof(f279,plain,(
% 0.20/0.49    spl7_23 <=> m1_subset_1(sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),u1_struct_0(sK3))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.20/0.49  fof(f349,plain,(
% 0.20/0.49    ~m1_subset_1(sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),u1_struct_0(sK3)) | ~l1_orders_2(sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | (~spl7_2 | spl7_18)),
% 0.20/0.49    inference(subsumption_resolution,[],[f348,f77])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    m1_subset_1(sK4,u1_struct_0(sK3)) | ~spl7_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f75])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    spl7_2 <=> m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.49  fof(f348,plain,(
% 0.20/0.49    ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~m1_subset_1(sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),u1_struct_0(sK3)) | ~l1_orders_2(sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | spl7_18),
% 0.20/0.49    inference(subsumption_resolution,[],[f327,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.49  fof(f327,plain,(
% 0.20/0.49    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~m1_subset_1(sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),u1_struct_0(sK3)) | ~l1_orders_2(sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | spl7_18),
% 0.20/0.49    inference(resolution,[],[f57,f224])).
% 0.20/0.49  fof(f224,plain,(
% 0.20/0.49    ~sP1(sK3,sK4,sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),k1_xboole_0) | spl7_18),
% 0.20/0.49    inference(avatar_component_clause,[],[f222])).
% 0.20/0.49  fof(f222,plain,(
% 0.20/0.49    spl7_18 <=> sP1(sK3,sK4,sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (sP1(X0,X2,X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (sP1(X0,X2,X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(definition_folding,[],[f17,f25,f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X3,X1,X2,X0] : (sP0(X3,X1,X2,X0) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.49  % (31462)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X2,X1,X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> sP0(X3,X1,X2,X0)) | ~sP1(X0,X2,X1,X3))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).
% 0.20/0.49  fof(f282,plain,(
% 0.20/0.49    spl7_23 | ~spl7_12 | ~spl7_19),
% 0.20/0.49    inference(avatar_split_clause,[],[f268,f239,f134,f279])).
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    spl7_12 <=> r2_hidden(sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),k3_orders_2(sK3,k1_xboole_0,sK4))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.20/0.49  fof(f239,plain,(
% 0.20/0.49    spl7_19 <=> m1_subset_1(k3_orders_2(sK3,k1_xboole_0,sK4),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.20/0.49  fof(f268,plain,(
% 0.20/0.49    m1_subset_1(sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),u1_struct_0(sK3)) | (~spl7_12 | ~spl7_19)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f136,f241,f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.49    inference(flattening,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.49  fof(f241,plain,(
% 0.20/0.49    m1_subset_1(k3_orders_2(sK3,k1_xboole_0,sK4),k1_zfmisc_1(u1_struct_0(sK3))) | ~spl7_19),
% 0.20/0.49    inference(avatar_component_clause,[],[f239])).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    r2_hidden(sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),k3_orders_2(sK3,k1_xboole_0,sK4)) | ~spl7_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f134])).
% 0.20/0.49  fof(f242,plain,(
% 0.20/0.49    spl7_19 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f234,f100,f95,f90,f85,f80,f75,f239])).
% 0.20/0.49  fof(f234,plain,(
% 0.20/0.49    m1_subset_1(k3_orders_2(sK3,k1_xboole_0,sK4),k1_zfmisc_1(u1_struct_0(sK3))) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f102,f97,f92,f87,f82,f77,f49,f62])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).
% 0.20/0.49  fof(f227,plain,(
% 0.20/0.49    ~spl7_18 | ~spl7_12 | ~spl7_15),
% 0.20/0.49    inference(avatar_split_clause,[],[f226,f166,f134,f222])).
% 0.20/0.49  fof(f166,plain,(
% 0.20/0.49    spl7_15 <=> sP6(k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.20/0.49  fof(f226,plain,(
% 0.20/0.49    ~sP1(sK3,sK4,sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),k1_xboole_0) | (~spl7_12 | ~spl7_15)),
% 0.20/0.49    inference(subsumption_resolution,[],[f218,f199])).
% 0.20/0.49  fof(f199,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~sP0(k1_xboole_0,X0,X1,X2)) ) | ~spl7_15),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f183,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | r2_hidden(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ~r2_hidden(X1,X0) | ~r2_orders_2(X3,X1,X2)) & ((r2_hidden(X1,X0) & r2_orders_2(X3,X1,X2)) | ~sP0(X0,X1,X2,X3)))),
% 0.20/0.49    inference(rectify,[],[f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ! [X3,X1,X2,X0] : ((sP0(X3,X1,X2,X0) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~sP0(X3,X1,X2,X0)))),
% 0.20/0.49    inference(flattening,[],[f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X3,X1,X2,X0] : ((sP0(X3,X1,X2,X0) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~sP0(X3,X1,X2,X0)))),
% 0.20/0.49    inference(nnf_transformation,[],[f24])).
% 0.20/0.49  fof(f183,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl7_15),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f168,f68])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP6(X1)) )),
% 0.20/0.49    inference(general_splitting,[],[f64,f67_D])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP6(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f67_D])).
% 0.20/0.49  fof(f67_D,plain,(
% 0.20/0.49    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP6(X1)) )),
% 0.20/0.49    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.49  fof(f168,plain,(
% 0.20/0.49    sP6(k1_xboole_0) | ~spl7_15),
% 0.20/0.49    inference(avatar_component_clause,[],[f166])).
% 0.20/0.49  fof(f218,plain,(
% 0.20/0.49    sP0(k1_xboole_0,sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),sK4,sK3) | ~sP1(sK3,sK4,sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),k1_xboole_0) | ~spl7_12),
% 0.20/0.49    inference(resolution,[],[f52,f136])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,k3_orders_2(X0,X3,X1)) | sP0(X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (((r2_hidden(X2,k3_orders_2(X0,X3,X1)) | ~sP0(X3,X2,X1,X0)) & (sP0(X3,X2,X1,X0) | ~r2_hidden(X2,k3_orders_2(X0,X3,X1)))) | ~sP1(X0,X1,X2,X3))),
% 0.20/0.49    inference(rectify,[],[f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X0,X2,X1,X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~sP0(X3,X1,X2,X0)) & (sP0(X3,X1,X2,X0) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~sP1(X0,X2,X1,X3))),
% 0.20/0.49    inference(nnf_transformation,[],[f25])).
% 0.20/0.49  fof(f169,plain,(
% 0.20/0.49    spl7_15 | ~spl7_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f162,f105,f166])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    spl7_8 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.49  fof(f162,plain,(
% 0.20/0.49    sP6(k1_xboole_0) | ~spl7_8),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f107,f49,f67])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0) | ~spl7_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f105])).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    spl7_12 | spl7_11),
% 0.20/0.49    inference(avatar_split_clause,[],[f131,f126,f134])).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    spl7_11 <=> k1_xboole_0 = k3_orders_2(sK3,k1_xboole_0,sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.49  % (31462)Refutation not found, incomplete strategy% (31462)------------------------------
% 0.20/0.49  % (31462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    r2_hidden(sK5(k3_orders_2(sK3,k1_xboole_0,sK4)),k3_orders_2(sK3,k1_xboole_0,sK4)) | spl7_11),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f128,f60])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ! [X0] : ((sP2(sK5(X0),X0) & r2_hidden(sK5(X0),X0)) | k1_xboole_0 = X0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ! [X0] : (? [X1] : (sP2(X1,X0) & r2_hidden(X1,X0)) => (sP2(sK5(X0),X0) & r2_hidden(sK5(X0),X0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0] : (? [X1] : (sP2(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.49    inference(definition_folding,[],[f18,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X1,X0] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP2(X1,X0))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).
% 0.20/0.49  % (31462)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (31462)Memory used [KB]: 10618
% 0.20/0.49  % (31462)Time elapsed: 0.071 s
% 0.20/0.49  % (31462)------------------------------
% 0.20/0.49  % (31462)------------------------------
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    k1_xboole_0 != k3_orders_2(sK3,k1_xboole_0,sK4) | spl7_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f126])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    ~spl7_11 | spl7_1 | ~spl7_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f124,f112,f70,f126])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    spl7_1 <=> k1_xboole_0 = k3_orders_2(sK3,k1_struct_0(sK3),sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    spl7_9 <=> l1_struct_0(sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    k1_xboole_0 != k3_orders_2(sK3,k1_xboole_0,sK4) | (spl7_1 | ~spl7_9)),
% 0.20/0.49    inference(subsumption_resolution,[],[f118,f114])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    l1_struct_0(sK3) | ~spl7_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f112])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    k1_xboole_0 != k3_orders_2(sK3,k1_xboole_0,sK4) | ~l1_struct_0(sK3) | spl7_1),
% 0.20/0.49    inference(superposition,[],[f72,f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    k1_xboole_0 != k3_orders_2(sK3,k1_struct_0(sK3),sK4) | spl7_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f70])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    spl7_9 | ~spl7_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f110,f80,f112])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    l1_struct_0(sK3) | ~spl7_3),
% 0.20/0.49    inference(resolution,[],[f51,f82])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    spl7_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f48,f105])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    ~spl7_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f41,f100])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ~v2_struct_0(sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    (k1_xboole_0 != k3_orders_2(sK3,k1_struct_0(sK3),sK4) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f13,f30,f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 != k3_orders_2(sK3,k1_struct_0(sK3),X1) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ? [X1] : (k1_xboole_0 != k3_orders_2(sK3,k1_struct_0(sK3),X1) & m1_subset_1(X1,u1_struct_0(sK3))) => (k1_xboole_0 != k3_orders_2(sK3,k1_struct_0(sK3),sK4) & m1_subset_1(sK4,u1_struct_0(sK3)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1)))),
% 0.20/0.49    inference(negated_conjecture,[],[f10])).
% 0.20/0.49  fof(f10,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_orders_2)).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    spl7_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f42,f95])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    v3_orders_2(sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    spl7_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f43,f90])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    v4_orders_2(sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    spl7_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f44,f85])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    v5_orders_2(sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    spl7_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f45,f80])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    l1_orders_2(sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    spl7_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f46,f75])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ~spl7_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f47,f70])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    k1_xboole_0 != k3_orders_2(sK3,k1_struct_0(sK3),sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (31458)------------------------------
% 0.20/0.49  % (31458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (31458)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (31458)Memory used [KB]: 10874
% 0.20/0.49  % (31458)Time elapsed: 0.018 s
% 0.20/0.49  % (31458)------------------------------
% 0.20/0.49  % (31458)------------------------------
% 0.20/0.49  % (31445)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (31439)Success in time 0.132 s
%------------------------------------------------------------------------------
