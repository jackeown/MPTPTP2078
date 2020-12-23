%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:57 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 409 expanded)
%              Number of leaves         :   22 ( 122 expanded)
%              Depth                    :   24
%              Number of atoms          :  557 (3742 expanded)
%              Number of equality atoms :   30 (  52 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f362,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f93,f117,f308,f313,f348])).

fof(f348,plain,
    ( ~ spl8_1
    | ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f347])).

fof(f347,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f316,f95])).

fof(f95,plain,(
    ! [X1] : ~ v1_subset_1(X1,X1) ),
    inference(subsumption_resolution,[],[f83,f94])).

fof(f94,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f62,f61])).

fof(f61,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f83,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f316,plain,
    ( v1_subset_1(sK4,sK4)
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(backward_demodulation,[],[f86,f121])).

% (9236)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f121,plain,
    ( u1_struct_0(sK3) = sK4
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl8_3
  <=> u1_struct_0(sK3) = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f86,plain,
    ( v1_subset_1(sK4,u1_struct_0(sK3))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl8_1
  <=> v1_subset_1(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f313,plain,
    ( spl8_3
    | ~ spl8_2
    | spl8_6 ),
    inference(avatar_split_clause,[],[f312,f305,f89,f119])).

fof(f89,plain,
    ( spl8_2
  <=> r2_hidden(k3_yellow_0(sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f305,plain,
    ( spl8_6
  <=> r2_hidden(sK7(u1_struct_0(sK3),u1_struct_0(sK3),sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f312,plain,
    ( u1_struct_0(sK3) = sK4
    | ~ spl8_2
    | spl8_6 ),
    inference(subsumption_resolution,[],[f311,f94])).

fof(f311,plain,
    ( u1_struct_0(sK3) = sK4
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl8_2
    | spl8_6 ),
    inference(subsumption_resolution,[],[f309,f58])).

fof(f58,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( r2_hidden(k3_yellow_0(sK3),sK4)
      | ~ v1_subset_1(sK4,u1_struct_0(sK3)) )
    & ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
      | v1_subset_1(sK4,u1_struct_0(sK3)) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v13_waybel_0(sK4,sK3)
    & v2_waybel_0(sK4,sK3)
    & ~ v1_xboole_0(sK4)
    & l1_orders_2(sK3)
    & v1_yellow_0(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f34,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | v1_subset_1(X1,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(sK3),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK3)) )
          & ( ~ r2_hidden(k3_yellow_0(sK3),X1)
            | v1_subset_1(X1,u1_struct_0(sK3)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
          & v13_waybel_0(X1,sK3)
          & v2_waybel_0(X1,sK3)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK3)
      & v1_yellow_0(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ( r2_hidden(k3_yellow_0(sK3),X1)
          | ~ v1_subset_1(X1,u1_struct_0(sK3)) )
        & ( ~ r2_hidden(k3_yellow_0(sK3),X1)
          | v1_subset_1(X1,u1_struct_0(sK3)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        & v13_waybel_0(X1,sK3)
        & v2_waybel_0(X1,sK3)
        & ~ v1_xboole_0(X1) )
   => ( ( r2_hidden(k3_yellow_0(sK3),sK4)
        | ~ v1_subset_1(sK4,u1_struct_0(sK3)) )
      & ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
        | v1_subset_1(sK4,u1_struct_0(sK3)) )
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
      & v13_waybel_0(sK4,sK3)
      & v2_waybel_0(sK4,sK3)
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f309,plain,
    ( u1_struct_0(sK3) = sK4
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl8_2
    | spl8_6 ),
    inference(resolution,[],[f307,f224])).

fof(f224,plain,
    ( ! [X8,X9] :
        ( r2_hidden(sK7(u1_struct_0(sK3),X8,X9),sK4)
        | X8 = X9
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK3))) )
    | ~ spl8_2 ),
    inference(resolution,[],[f216,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),X0)
      | X1 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( sP2(X2,sK7(X0,X1,X2),X1)
            & m1_subset_1(sK7(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( sP2(X2,X3,X1)
          & m1_subset_1(X3,X0) )
     => ( sP2(X2,sK7(X0,X1,X2),X1)
        & m1_subset_1(sK7(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( sP2(X2,X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_folding,[],[f25,f31])).

fof(f31,plain,(
    ! [X2,X3,X1] :
      ( ( r2_hidden(X3,X1)
      <~> r2_hidden(X3,X2) )
      | ~ sP2(X2,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

fof(f216,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r2_hidden(X0,sK4) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f215,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f215,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | v2_struct_0(sK3) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f214,f52])).

fof(f52,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f214,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3)
        | v2_struct_0(sK3) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f213,f53])).

fof(f53,plain,(
    v1_yellow_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f213,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ v1_yellow_0(sK3)
        | ~ v5_orders_2(sK3)
        | v2_struct_0(sK3) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f212,f54])).

fof(f54,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f212,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | ~ v1_yellow_0(sK3)
        | ~ v5_orders_2(sK3)
        | v2_struct_0(sK3) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f209,f104])).

fof(f104,plain,(
    sP0(sK4,sK3) ),
    inference(subsumption_resolution,[],[f103,f57])).

fof(f57,plain,(
    v13_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f103,plain,
    ( ~ v13_waybel_0(sK4,sK3)
    | sP0(sK4,sK3) ),
    inference(resolution,[],[f101,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v13_waybel_0(X1,X0)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v13_waybel_0(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f101,plain,(
    sP1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f99,f54])).

fof(f99,plain,
    ( sP1(sK3,sK4)
    | ~ l1_orders_2(sK3) ),
    inference(resolution,[],[f72,f58])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f17,f29,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r1_orders_2(X0,X2,X3)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f209,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ sP0(sK4,sK3)
        | ~ l1_orders_2(sK3)
        | ~ v1_yellow_0(sK3)
        | ~ v5_orders_2(sK3)
        | v2_struct_0(sK3) )
    | ~ spl8_2 ),
    inference(resolution,[],[f179,f91])).

fof(f91,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f179,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(k3_yellow_0(X5),X4)
      | r2_hidden(X3,X4)
      | ~ m1_subset_1(X3,u1_struct_0(X5))
      | ~ sP0(X4,X5)
      | ~ l1_orders_2(X5)
      | ~ v1_yellow_0(X5)
      | ~ v5_orders_2(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f176,f63])).

fof(f63,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f176,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(X3,X4)
      | ~ r2_hidden(k3_yellow_0(X5),X4)
      | ~ m1_subset_1(X3,u1_struct_0(X5))
      | ~ m1_subset_1(k3_yellow_0(X5),u1_struct_0(X5))
      | ~ sP0(X4,X5)
      | ~ l1_orders_2(X5)
      | ~ v1_yellow_0(X5)
      | ~ v5_orders_2(X5)
      | v2_struct_0(X5) ) ),
    inference(duplicate_literal_removal,[],[f175])).

fof(f175,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(X3,X4)
      | ~ r2_hidden(k3_yellow_0(X5),X4)
      | ~ m1_subset_1(X3,u1_struct_0(X5))
      | ~ m1_subset_1(k3_yellow_0(X5),u1_struct_0(X5))
      | ~ sP0(X4,X5)
      | ~ m1_subset_1(X3,u1_struct_0(X5))
      | ~ l1_orders_2(X5)
      | ~ v1_yellow_0(X5)
      | ~ v5_orders_2(X5)
      | v2_struct_0(X5) ) ),
    inference(resolution,[],[f66,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

fof(f66,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r1_orders_2(X1,X4,X5)
      | r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X0)
          & r1_orders_2(X1,sK5(X0,X1),sK6(X0,X1))
          & r2_hidden(sK5(X0,X1),X0)
          & m1_subset_1(sK6(X0,X1),u1_struct_0(X1))
          & m1_subset_1(sK5(X0,X1),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
                | ~ r1_orders_2(X1,X4,X5)
                | ~ r2_hidden(X4,X0)
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f40,f42,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X0)
              & r1_orders_2(X1,X2,X3)
              & r2_hidden(X2,X0)
              & m1_subset_1(X3,u1_struct_0(X1)) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X0)
            & r1_orders_2(X1,sK5(X0,X1),X3)
            & r2_hidden(sK5(X0,X1),X0)
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

% (9233)Refutation not found, incomplete strategy% (9233)------------------------------
% (9233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9233)Termination reason: Refutation not found, incomplete strategy

% (9233)Memory used [KB]: 6140
% (9233)Time elapsed: 0.079 s
% (9233)------------------------------
% (9233)------------------------------
fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X0)
          & r1_orders_2(X1,sK5(X0,X1),X3)
          & r2_hidden(sK5(X0,X1),X0)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r2_hidden(sK6(X0,X1),X0)
        & r1_orders_2(X1,sK5(X0,X1),sK6(X0,X1))
        & r2_hidden(sK5(X0,X1),X0)
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X3,X0)
                & r1_orders_2(X1,X2,X3)
                & r2_hidden(X2,X0)
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & m1_subset_1(X2,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
                | ~ r1_orders_2(X1,X4,X5)
                | ~ r2_hidden(X4,X0)
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r1_orders_2(X0,X2,X3)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X2] :
            ( ! [X3] :
                ( r2_hidden(X3,X1)
                | ~ r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f307,plain,
    ( ~ r2_hidden(sK7(u1_struct_0(sK3),u1_struct_0(sK3),sK4),sK4)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f305])).

fof(f308,plain,
    ( ~ spl8_6
    | spl8_3
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f303,f89,f119,f305])).

fof(f303,plain,
    ( u1_struct_0(sK3) = sK4
    | ~ r2_hidden(sK7(u1_struct_0(sK3),u1_struct_0(sK3),sK4),sK4)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f301,f94])).

fof(f301,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(sK3) = sK4
    | ~ r2_hidden(sK7(u1_struct_0(sK3),u1_struct_0(sK3),sK4),sK4)
    | ~ spl8_2 ),
    inference(resolution,[],[f298,f129])).

fof(f129,plain,(
    ! [X2] :
      ( r2_hidden(X2,u1_struct_0(sK3))
      | ~ r2_hidden(X2,sK4) ) ),
    inference(resolution,[],[f77,f58])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f298,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK7(u1_struct_0(sK3),X0,sK4),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | sK4 = X0 )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f297,f58])).

fof(f297,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r2_hidden(sK7(u1_struct_0(sK3),X0,sK4),X0)
        | sK4 = X0 )
    | ~ spl8_2 ),
    inference(duplicate_literal_removal,[],[f294])).

fof(f294,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r2_hidden(sK7(u1_struct_0(sK3),X0,sK4),X0)
        | sK4 = X0
        | sK4 = X0
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) )
    | ~ spl8_2 ),
    inference(resolution,[],[f159,f224])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X2,X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
      | ~ r2_hidden(sK7(X2,X0,X1),X0)
      | X0 = X1 ) ),
    inference(resolution,[],[f81,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( ~ r2_hidden(X1,X0)
          | ~ r2_hidden(X1,X2) )
        & ( r2_hidden(X1,X0)
          | r2_hidden(X1,X2) ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X2,X3,X1] :
      ( ( ( ~ r2_hidden(X3,X2)
          | ~ r2_hidden(X3,X1) )
        & ( r2_hidden(X3,X2)
          | r2_hidden(X3,X1) ) )
      | ~ sP2(X2,X3,X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,sK7(X0,X1,X2),X1)
      | X1 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f117,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f115,f54])).

fof(f115,plain,
    ( ~ l1_orders_2(sK3)
    | spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f113,f98])).

fof(f98,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK3),sK4)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f96,f55])).

fof(f55,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f96,plain,
    ( v1_xboole_0(sK4)
    | ~ m1_subset_1(k3_yellow_0(sK3),sK4)
    | spl8_2 ),
    inference(resolution,[],[f74,f90])).

fof(f90,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f113,plain,
    ( m1_subset_1(k3_yellow_0(sK3),sK4)
    | ~ l1_orders_2(sK3)
    | spl8_1 ),
    inference(superposition,[],[f63,f107])).

fof(f107,plain,
    ( u1_struct_0(sK3) = sK4
    | spl8_1 ),
    inference(subsumption_resolution,[],[f105,f87])).

fof(f87,plain,
    ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f105,plain,
    ( u1_struct_0(sK3) = sK4
    | v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(resolution,[],[f76,f58])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f93,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f59,f89,f85])).

fof(f59,plain,
    ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f37])).

fof(f92,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f60,f89,f85])).

fof(f60,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4)
    | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 20:42:22 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.48  % (9232)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.49  % (9241)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.23/0.49  % (9250)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.23/0.50  % (9232)Refutation found. Thanks to Tanya!
% 0.23/0.50  % SZS status Theorem for theBenchmark
% 0.23/0.50  % (9233)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.50  % SZS output start Proof for theBenchmark
% 0.23/0.50  fof(f362,plain,(
% 0.23/0.50    $false),
% 0.23/0.50    inference(avatar_sat_refutation,[],[f92,f93,f117,f308,f313,f348])).
% 0.23/0.50  fof(f348,plain,(
% 0.23/0.50    ~spl8_1 | ~spl8_3),
% 0.23/0.50    inference(avatar_contradiction_clause,[],[f347])).
% 0.23/0.50  fof(f347,plain,(
% 0.23/0.50    $false | (~spl8_1 | ~spl8_3)),
% 0.23/0.50    inference(subsumption_resolution,[],[f316,f95])).
% 0.23/0.50  fof(f95,plain,(
% 0.23/0.50    ( ! [X1] : (~v1_subset_1(X1,X1)) )),
% 0.23/0.50    inference(subsumption_resolution,[],[f83,f94])).
% 0.23/0.50  fof(f94,plain,(
% 0.23/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.23/0.50    inference(forward_demodulation,[],[f62,f61])).
% 0.23/0.50  fof(f61,plain,(
% 0.23/0.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.23/0.50    inference(cnf_transformation,[],[f1])).
% 0.23/0.50  fof(f1,axiom,(
% 0.23/0.50    ! [X0] : k2_subset_1(X0) = X0),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.23/0.50  fof(f62,plain,(
% 0.23/0.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.23/0.50    inference(cnf_transformation,[],[f2])).
% 0.23/0.50  fof(f2,axiom,(
% 0.23/0.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.23/0.50  fof(f83,plain,(
% 0.23/0.50    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 0.23/0.50    inference(equality_resolution,[],[f75])).
% 0.23/0.50  fof(f75,plain,(
% 0.23/0.50    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.23/0.50    inference(cnf_transformation,[],[f44])).
% 0.23/0.50  fof(f44,plain,(
% 0.23/0.50    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.50    inference(nnf_transformation,[],[f22])).
% 0.23/0.50  fof(f22,plain,(
% 0.23/0.50    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.50    inference(ennf_transformation,[],[f10])).
% 0.23/0.50  fof(f10,axiom,(
% 0.23/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.23/0.50  fof(f316,plain,(
% 0.23/0.50    v1_subset_1(sK4,sK4) | (~spl8_1 | ~spl8_3)),
% 0.23/0.50    inference(backward_demodulation,[],[f86,f121])).
% 0.23/0.50  % (9236)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.23/0.50  fof(f121,plain,(
% 0.23/0.50    u1_struct_0(sK3) = sK4 | ~spl8_3),
% 0.23/0.50    inference(avatar_component_clause,[],[f119])).
% 0.23/0.50  fof(f119,plain,(
% 0.23/0.50    spl8_3 <=> u1_struct_0(sK3) = sK4),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.23/0.50  fof(f86,plain,(
% 0.23/0.50    v1_subset_1(sK4,u1_struct_0(sK3)) | ~spl8_1),
% 0.23/0.50    inference(avatar_component_clause,[],[f85])).
% 0.23/0.50  fof(f85,plain,(
% 0.23/0.50    spl8_1 <=> v1_subset_1(sK4,u1_struct_0(sK3))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.23/0.50  fof(f313,plain,(
% 0.23/0.50    spl8_3 | ~spl8_2 | spl8_6),
% 0.23/0.50    inference(avatar_split_clause,[],[f312,f305,f89,f119])).
% 0.23/0.50  fof(f89,plain,(
% 0.23/0.50    spl8_2 <=> r2_hidden(k3_yellow_0(sK3),sK4)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.23/0.50  fof(f305,plain,(
% 0.23/0.50    spl8_6 <=> r2_hidden(sK7(u1_struct_0(sK3),u1_struct_0(sK3),sK4),sK4)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.23/0.50  fof(f312,plain,(
% 0.23/0.50    u1_struct_0(sK3) = sK4 | (~spl8_2 | spl8_6)),
% 0.23/0.50    inference(subsumption_resolution,[],[f311,f94])).
% 0.23/0.50  fof(f311,plain,(
% 0.23/0.50    u1_struct_0(sK3) = sK4 | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) | (~spl8_2 | spl8_6)),
% 0.23/0.50    inference(subsumption_resolution,[],[f309,f58])).
% 0.23/0.50  fof(f58,plain,(
% 0.23/0.50    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.23/0.50    inference(cnf_transformation,[],[f37])).
% 0.23/0.50  fof(f37,plain,(
% 0.23/0.50    ((r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(sK4,sK3) & v2_waybel_0(sK4,sK3) & ~v1_xboole_0(sK4)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 0.23/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f34,f36,f35])).
% 0.23/0.50  fof(f35,plain,(
% 0.23/0.50    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK3),X1) | ~v1_subset_1(X1,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),X1) | v1_subset_1(X1,u1_struct_0(sK3))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(X1,sK3) & v2_waybel_0(X1,sK3) & ~v1_xboole_0(X1)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f36,plain,(
% 0.23/0.50    ? [X1] : ((r2_hidden(k3_yellow_0(sK3),X1) | ~v1_subset_1(X1,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),X1) | v1_subset_1(X1,u1_struct_0(sK3))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(X1,sK3) & v2_waybel_0(X1,sK3) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(sK4,sK3) & v2_waybel_0(sK4,sK3) & ~v1_xboole_0(sK4))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f34,plain,(
% 0.23/0.50    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.23/0.50    inference(flattening,[],[f33])).
% 0.23/0.50  fof(f33,plain,(
% 0.23/0.50    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.23/0.50    inference(nnf_transformation,[],[f14])).
% 0.23/0.50  fof(f14,plain,(
% 0.23/0.50    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.23/0.50    inference(flattening,[],[f13])).
% 0.23/0.50  fof(f13,plain,(
% 0.23/0.50    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.23/0.50    inference(ennf_transformation,[],[f12])).
% 0.23/0.50  fof(f12,negated_conjecture,(
% 0.23/0.50    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.23/0.50    inference(negated_conjecture,[],[f11])).
% 0.23/0.50  fof(f11,conjecture,(
% 0.23/0.50    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 0.23/0.50  fof(f309,plain,(
% 0.23/0.50    u1_struct_0(sK3) = sK4 | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) | (~spl8_2 | spl8_6)),
% 0.23/0.50    inference(resolution,[],[f307,f224])).
% 0.23/0.50  fof(f224,plain,(
% 0.23/0.50    ( ! [X8,X9] : (r2_hidden(sK7(u1_struct_0(sK3),X8,X9),sK4) | X8 = X9 | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK3)))) ) | ~spl8_2),
% 0.23/0.50    inference(resolution,[],[f216,f80])).
% 0.23/0.50  fof(f80,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (m1_subset_1(sK7(X0,X1,X2),X0) | X1 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.23/0.50    inference(cnf_transformation,[],[f48])).
% 0.23/0.50  fof(f48,plain,(
% 0.23/0.50    ! [X0,X1] : (! [X2] : (X1 = X2 | (sP2(X2,sK7(X0,X1,X2),X1) & m1_subset_1(sK7(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f47])).
% 0.23/0.50  fof(f47,plain,(
% 0.23/0.50    ! [X2,X1,X0] : (? [X3] : (sP2(X2,X3,X1) & m1_subset_1(X3,X0)) => (sP2(X2,sK7(X0,X1,X2),X1) & m1_subset_1(sK7(X0,X1,X2),X0)))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f32,plain,(
% 0.23/0.50    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (sP2(X2,X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.50    inference(definition_folding,[],[f25,f31])).
% 0.23/0.50  fof(f31,plain,(
% 0.23/0.50    ! [X2,X3,X1] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) | ~sP2(X2,X3,X1))),
% 0.23/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.23/0.50  fof(f25,plain,(
% 0.23/0.50    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.50    inference(flattening,[],[f24])).
% 0.23/0.50  fof(f24,plain,(
% 0.23/0.50    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.50    inference(ennf_transformation,[],[f4])).
% 0.23/0.50  fof(f4,axiom,(
% 0.23/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).
% 0.23/0.50  fof(f216,plain,(
% 0.23/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | r2_hidden(X0,sK4)) ) | ~spl8_2),
% 0.23/0.50    inference(subsumption_resolution,[],[f215,f49])).
% 0.23/0.50  fof(f49,plain,(
% 0.23/0.50    ~v2_struct_0(sK3)),
% 0.23/0.50    inference(cnf_transformation,[],[f37])).
% 0.23/0.50  fof(f215,plain,(
% 0.23/0.50    ( ! [X0] : (r2_hidden(X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK3)) | v2_struct_0(sK3)) ) | ~spl8_2),
% 0.23/0.50    inference(subsumption_resolution,[],[f214,f52])).
% 0.23/0.50  fof(f52,plain,(
% 0.23/0.50    v5_orders_2(sK3)),
% 0.23/0.50    inference(cnf_transformation,[],[f37])).
% 0.23/0.50  fof(f214,plain,(
% 0.23/0.50    ( ! [X0] : (r2_hidden(X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~v5_orders_2(sK3) | v2_struct_0(sK3)) ) | ~spl8_2),
% 0.23/0.50    inference(subsumption_resolution,[],[f213,f53])).
% 0.23/0.50  fof(f53,plain,(
% 0.23/0.50    v1_yellow_0(sK3)),
% 0.23/0.50    inference(cnf_transformation,[],[f37])).
% 0.23/0.50  fof(f213,plain,(
% 0.23/0.50    ( ! [X0] : (r2_hidden(X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~v1_yellow_0(sK3) | ~v5_orders_2(sK3) | v2_struct_0(sK3)) ) | ~spl8_2),
% 0.23/0.50    inference(subsumption_resolution,[],[f212,f54])).
% 0.23/0.50  fof(f54,plain,(
% 0.23/0.50    l1_orders_2(sK3)),
% 0.23/0.50    inference(cnf_transformation,[],[f37])).
% 0.23/0.50  fof(f212,plain,(
% 0.23/0.50    ( ! [X0] : (r2_hidden(X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~l1_orders_2(sK3) | ~v1_yellow_0(sK3) | ~v5_orders_2(sK3) | v2_struct_0(sK3)) ) | ~spl8_2),
% 0.23/0.50    inference(subsumption_resolution,[],[f209,f104])).
% 0.23/0.50  fof(f104,plain,(
% 0.23/0.50    sP0(sK4,sK3)),
% 0.23/0.50    inference(subsumption_resolution,[],[f103,f57])).
% 0.23/0.50  fof(f57,plain,(
% 0.23/0.50    v13_waybel_0(sK4,sK3)),
% 0.23/0.50    inference(cnf_transformation,[],[f37])).
% 0.23/0.50  fof(f103,plain,(
% 0.23/0.50    ~v13_waybel_0(sK4,sK3) | sP0(sK4,sK3)),
% 0.23/0.50    inference(resolution,[],[f101,f64])).
% 0.23/0.50  fof(f64,plain,(
% 0.23/0.50    ( ! [X0,X1] : (~sP1(X0,X1) | ~v13_waybel_0(X1,X0) | sP0(X1,X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f38])).
% 0.23/0.50  fof(f38,plain,(
% 0.23/0.50    ! [X0,X1] : (((v13_waybel_0(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v13_waybel_0(X1,X0))) | ~sP1(X0,X1))),
% 0.23/0.50    inference(nnf_transformation,[],[f29])).
% 0.23/0.50  fof(f29,plain,(
% 0.23/0.50    ! [X0,X1] : ((v13_waybel_0(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.23/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.23/0.50  fof(f101,plain,(
% 0.23/0.50    sP1(sK3,sK4)),
% 0.23/0.50    inference(subsumption_resolution,[],[f99,f54])).
% 0.23/0.50  fof(f99,plain,(
% 0.23/0.50    sP1(sK3,sK4) | ~l1_orders_2(sK3)),
% 0.23/0.50    inference(resolution,[],[f72,f58])).
% 0.23/0.50  fof(f72,plain,(
% 0.23/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1) | ~l1_orders_2(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f30])).
% 0.23/0.50  fof(f30,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.23/0.50    inference(definition_folding,[],[f17,f29,f28])).
% 0.23/0.50  fof(f28,plain,(
% 0.23/0.50    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))))),
% 0.23/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.23/0.50  fof(f17,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.23/0.50    inference(flattening,[],[f16])).
% 0.23/0.50  fof(f16,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.23/0.50    inference(ennf_transformation,[],[f9])).
% 0.23/0.50  fof(f9,axiom,(
% 0.23/0.50    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).
% 0.23/0.50  fof(f209,plain,(
% 0.23/0.50    ( ! [X0] : (r2_hidden(X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~sP0(sK4,sK3) | ~l1_orders_2(sK3) | ~v1_yellow_0(sK3) | ~v5_orders_2(sK3) | v2_struct_0(sK3)) ) | ~spl8_2),
% 0.23/0.50    inference(resolution,[],[f179,f91])).
% 0.23/0.50  fof(f91,plain,(
% 0.23/0.50    r2_hidden(k3_yellow_0(sK3),sK4) | ~spl8_2),
% 0.23/0.50    inference(avatar_component_clause,[],[f89])).
% 0.23/0.50  fof(f179,plain,(
% 0.23/0.50    ( ! [X4,X5,X3] : (~r2_hidden(k3_yellow_0(X5),X4) | r2_hidden(X3,X4) | ~m1_subset_1(X3,u1_struct_0(X5)) | ~sP0(X4,X5) | ~l1_orders_2(X5) | ~v1_yellow_0(X5) | ~v5_orders_2(X5) | v2_struct_0(X5)) )),
% 0.23/0.50    inference(subsumption_resolution,[],[f176,f63])).
% 0.23/0.50  fof(f63,plain,(
% 0.23/0.50    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f15])).
% 0.23/0.50  fof(f15,plain,(
% 0.23/0.50    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.23/0.50    inference(ennf_transformation,[],[f7])).
% 0.23/0.50  fof(f7,axiom,(
% 0.23/0.50    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 0.23/0.50  fof(f176,plain,(
% 0.23/0.50    ( ! [X4,X5,X3] : (r2_hidden(X3,X4) | ~r2_hidden(k3_yellow_0(X5),X4) | ~m1_subset_1(X3,u1_struct_0(X5)) | ~m1_subset_1(k3_yellow_0(X5),u1_struct_0(X5)) | ~sP0(X4,X5) | ~l1_orders_2(X5) | ~v1_yellow_0(X5) | ~v5_orders_2(X5) | v2_struct_0(X5)) )),
% 0.23/0.50    inference(duplicate_literal_removal,[],[f175])).
% 0.23/0.50  fof(f175,plain,(
% 0.23/0.50    ( ! [X4,X5,X3] : (r2_hidden(X3,X4) | ~r2_hidden(k3_yellow_0(X5),X4) | ~m1_subset_1(X3,u1_struct_0(X5)) | ~m1_subset_1(k3_yellow_0(X5),u1_struct_0(X5)) | ~sP0(X4,X5) | ~m1_subset_1(X3,u1_struct_0(X5)) | ~l1_orders_2(X5) | ~v1_yellow_0(X5) | ~v5_orders_2(X5) | v2_struct_0(X5)) )),
% 0.23/0.50    inference(resolution,[],[f66,f73])).
% 0.23/0.50  fof(f73,plain,(
% 0.23/0.50    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f19])).
% 0.23/0.50  fof(f19,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.23/0.50    inference(flattening,[],[f18])).
% 0.23/0.50  fof(f18,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.23/0.50    inference(ennf_transformation,[],[f8])).
% 0.23/0.50  fof(f8,axiom,(
% 0.23/0.50    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).
% 0.23/0.50  fof(f66,plain,(
% 0.23/0.50    ( ! [X4,X0,X5,X1] : (~r1_orders_2(X1,X4,X5) | r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~sP0(X0,X1)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f43])).
% 0.23/0.50  fof(f43,plain,(
% 0.23/0.50    ! [X0,X1] : ((sP0(X0,X1) | ((~r2_hidden(sK6(X0,X1),X0) & r1_orders_2(X1,sK5(X0,X1),sK6(X0,X1)) & r2_hidden(sK5(X0,X1),X0) & m1_subset_1(sK6(X0,X1),u1_struct_0(X1))) & m1_subset_1(sK5(X0,X1),u1_struct_0(X1)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,X0) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1)))),
% 0.23/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f40,f42,f41])).
% 0.23/0.50  fof(f41,plain,(
% 0.23/0.50    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,X2,X3) & r2_hidden(X2,X0) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1))) => (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,sK5(X0,X1),X3) & r2_hidden(sK5(X0,X1),X0) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(sK5(X0,X1),u1_struct_0(X1))))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  % (9233)Refutation not found, incomplete strategy% (9233)------------------------------
% 0.23/0.50  % (9233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (9233)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.50  
% 0.23/0.50  % (9233)Memory used [KB]: 6140
% 0.23/0.50  % (9233)Time elapsed: 0.079 s
% 0.23/0.50  % (9233)------------------------------
% 0.23/0.50  % (9233)------------------------------
% 0.23/0.50  fof(f42,plain,(
% 0.23/0.50    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,sK5(X0,X1),X3) & r2_hidden(sK5(X0,X1),X0) & m1_subset_1(X3,u1_struct_0(X1))) => (~r2_hidden(sK6(X0,X1),X0) & r1_orders_2(X1,sK5(X0,X1),sK6(X0,X1)) & r2_hidden(sK5(X0,X1),X0) & m1_subset_1(sK6(X0,X1),u1_struct_0(X1))))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f40,plain,(
% 0.23/0.50    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,X2,X3) & r2_hidden(X2,X0) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,X0) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1)))),
% 0.23/0.50    inference(rectify,[],[f39])).
% 0.23/0.50  fof(f39,plain,(
% 0.23/0.50    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~sP0(X1,X0)))),
% 0.23/0.50    inference(nnf_transformation,[],[f28])).
% 0.23/0.50  fof(f307,plain,(
% 0.23/0.50    ~r2_hidden(sK7(u1_struct_0(sK3),u1_struct_0(sK3),sK4),sK4) | spl8_6),
% 0.23/0.50    inference(avatar_component_clause,[],[f305])).
% 0.23/0.50  fof(f308,plain,(
% 0.23/0.50    ~spl8_6 | spl8_3 | ~spl8_2),
% 0.23/0.50    inference(avatar_split_clause,[],[f303,f89,f119,f305])).
% 0.23/0.50  fof(f303,plain,(
% 0.23/0.50    u1_struct_0(sK3) = sK4 | ~r2_hidden(sK7(u1_struct_0(sK3),u1_struct_0(sK3),sK4),sK4) | ~spl8_2),
% 0.23/0.50    inference(subsumption_resolution,[],[f301,f94])).
% 0.23/0.50  fof(f301,plain,(
% 0.23/0.50    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) | u1_struct_0(sK3) = sK4 | ~r2_hidden(sK7(u1_struct_0(sK3),u1_struct_0(sK3),sK4),sK4) | ~spl8_2),
% 0.23/0.50    inference(resolution,[],[f298,f129])).
% 0.23/0.50  fof(f129,plain,(
% 0.23/0.50    ( ! [X2] : (r2_hidden(X2,u1_struct_0(sK3)) | ~r2_hidden(X2,sK4)) )),
% 0.23/0.50    inference(resolution,[],[f77,f58])).
% 0.23/0.50  fof(f77,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f23])).
% 0.23/0.50  fof(f23,plain,(
% 0.23/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.50    inference(ennf_transformation,[],[f3])).
% 0.23/0.50  fof(f3,axiom,(
% 0.23/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.23/0.50  fof(f298,plain,(
% 0.23/0.50    ( ! [X0] : (~r2_hidden(sK7(u1_struct_0(sK3),X0,sK4),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | sK4 = X0) ) | ~spl8_2),
% 0.23/0.50    inference(subsumption_resolution,[],[f297,f58])).
% 0.23/0.50  fof(f297,plain,(
% 0.23/0.50    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~r2_hidden(sK7(u1_struct_0(sK3),X0,sK4),X0) | sK4 = X0) ) | ~spl8_2),
% 0.23/0.50    inference(duplicate_literal_removal,[],[f294])).
% 0.23/0.50  fof(f294,plain,(
% 0.23/0.50    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~r2_hidden(sK7(u1_struct_0(sK3),X0,sK4),X0) | sK4 = X0 | sK4 = X0 | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))) ) | ~spl8_2),
% 0.23/0.50    inference(resolution,[],[f159,f224])).
% 0.23/0.50  fof(f159,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (~r2_hidden(sK7(X2,X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | ~r2_hidden(sK7(X2,X0,X1),X0) | X0 = X1) )),
% 0.23/0.50    inference(resolution,[],[f81,f79])).
% 0.23/0.50  fof(f79,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f46])).
% 0.23/0.50  fof(f46,plain,(
% 0.23/0.50    ! [X0,X1,X2] : (((~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & (r2_hidden(X1,X0) | r2_hidden(X1,X2))) | ~sP2(X0,X1,X2))),
% 0.23/0.50    inference(rectify,[],[f45])).
% 0.23/0.50  fof(f45,plain,(
% 0.23/0.50    ! [X2,X3,X1] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) | ~sP2(X2,X3,X1))),
% 0.23/0.50    inference(nnf_transformation,[],[f31])).
% 0.23/0.50  fof(f81,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (sP2(X2,sK7(X0,X1,X2),X1) | X1 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.23/0.50    inference(cnf_transformation,[],[f48])).
% 0.23/0.50  fof(f117,plain,(
% 0.23/0.50    spl8_1 | spl8_2),
% 0.23/0.50    inference(avatar_contradiction_clause,[],[f116])).
% 0.23/0.50  fof(f116,plain,(
% 0.23/0.50    $false | (spl8_1 | spl8_2)),
% 0.23/0.50    inference(subsumption_resolution,[],[f115,f54])).
% 0.23/0.50  fof(f115,plain,(
% 0.23/0.50    ~l1_orders_2(sK3) | (spl8_1 | spl8_2)),
% 0.23/0.50    inference(subsumption_resolution,[],[f113,f98])).
% 0.23/0.50  fof(f98,plain,(
% 0.23/0.50    ~m1_subset_1(k3_yellow_0(sK3),sK4) | spl8_2),
% 0.23/0.50    inference(subsumption_resolution,[],[f96,f55])).
% 0.23/0.50  fof(f55,plain,(
% 0.23/0.50    ~v1_xboole_0(sK4)),
% 0.23/0.50    inference(cnf_transformation,[],[f37])).
% 0.23/0.50  fof(f96,plain,(
% 0.23/0.50    v1_xboole_0(sK4) | ~m1_subset_1(k3_yellow_0(sK3),sK4) | spl8_2),
% 0.23/0.50    inference(resolution,[],[f74,f90])).
% 0.23/0.50  fof(f90,plain,(
% 0.23/0.50    ~r2_hidden(k3_yellow_0(sK3),sK4) | spl8_2),
% 0.23/0.50    inference(avatar_component_clause,[],[f89])).
% 0.23/0.50  fof(f74,plain,(
% 0.23/0.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f21])).
% 0.23/0.50  fof(f21,plain,(
% 0.23/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.23/0.50    inference(flattening,[],[f20])).
% 0.23/0.50  fof(f20,plain,(
% 0.23/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.23/0.50    inference(ennf_transformation,[],[f5])).
% 0.23/0.50  fof(f5,axiom,(
% 0.23/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.23/0.50  fof(f113,plain,(
% 0.23/0.50    m1_subset_1(k3_yellow_0(sK3),sK4) | ~l1_orders_2(sK3) | spl8_1),
% 0.23/0.50    inference(superposition,[],[f63,f107])).
% 0.23/0.50  fof(f107,plain,(
% 0.23/0.50    u1_struct_0(sK3) = sK4 | spl8_1),
% 0.23/0.50    inference(subsumption_resolution,[],[f105,f87])).
% 0.23/0.50  fof(f87,plain,(
% 0.23/0.50    ~v1_subset_1(sK4,u1_struct_0(sK3)) | spl8_1),
% 0.23/0.50    inference(avatar_component_clause,[],[f85])).
% 0.23/0.50  fof(f105,plain,(
% 0.23/0.50    u1_struct_0(sK3) = sK4 | v1_subset_1(sK4,u1_struct_0(sK3))),
% 0.23/0.50    inference(resolution,[],[f76,f58])).
% 0.23/0.50  fof(f76,plain,(
% 0.23/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f44])).
% 0.23/0.50  fof(f93,plain,(
% 0.23/0.50    spl8_1 | ~spl8_2),
% 0.23/0.50    inference(avatar_split_clause,[],[f59,f89,f85])).
% 0.23/0.50  fof(f59,plain,(
% 0.23/0.50    ~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))),
% 0.23/0.50    inference(cnf_transformation,[],[f37])).
% 0.23/0.50  fof(f92,plain,(
% 0.23/0.50    ~spl8_1 | spl8_2),
% 0.23/0.50    inference(avatar_split_clause,[],[f60,f89,f85])).
% 0.23/0.50  fof(f60,plain,(
% 0.23/0.50    r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))),
% 0.23/0.50    inference(cnf_transformation,[],[f37])).
% 0.23/0.50  % SZS output end Proof for theBenchmark
% 0.23/0.50  % (9232)------------------------------
% 0.23/0.50  % (9232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (9232)Termination reason: Refutation
% 0.23/0.50  
% 0.23/0.50  % (9232)Memory used [KB]: 6268
% 0.23/0.50  % (9232)Time elapsed: 0.079 s
% 0.23/0.50  % (9232)------------------------------
% 0.23/0.50  % (9232)------------------------------
% 0.23/0.50  % (9224)Success in time 0.132 s
%------------------------------------------------------------------------------
