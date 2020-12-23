%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:42 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 130 expanded)
%              Number of leaves         :   17 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  220 ( 430 expanded)
%              Number of equality atoms :   13 (  22 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f492,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f82,f115,f186,f486,f490])).

fof(f490,plain,(
    ~ spl6_19 ),
    inference(avatar_contradiction_clause,[],[f487])).

fof(f487,plain,
    ( $false
    | ~ spl6_19 ),
    inference(resolution,[],[f485,f85])).

fof(f85,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f83,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f83,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f40,f30])).

fof(f30,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f485,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k1_xboole_0,sK4(u1_struct_0(sK1)))),k1_xboole_0)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f483])).

fof(f483,plain,
    ( spl6_19
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k1_xboole_0,sK4(u1_struct_0(sK1)))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f486,plain,
    ( ~ spl6_1
    | spl6_19
    | spl6_2
    | ~ spl6_4
    | spl6_5
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f481,f183,f79,f74,f64,f483,f59])).

fof(f59,plain,
    ( spl6_1
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f64,plain,
    ( spl6_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f74,plain,
    ( spl6_4
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f79,plain,
    ( spl6_5
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f183,plain,
    ( spl6_12
  <=> r2_waybel_0(sK0,sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f481,plain,
    ( v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0)
    | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k1_xboole_0,sK4(u1_struct_0(sK1)))),k1_xboole_0)
    | ~ l1_struct_0(sK0)
    | ~ spl6_12 ),
    inference(resolution,[],[f187,f185])).

fof(f185,plain,
    ( r2_waybel_0(sK0,sK1,k1_xboole_0)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f183])).

fof(f187,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_waybel_0(X0,X1,X2)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,sK4(u1_struct_0(X1)))),X2)
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f36,f38])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2)
      | ~ r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).

fof(f186,plain,
    ( spl6_12
    | spl6_3
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f180,f113,f69,f183])).

fof(f69,plain,
    ( spl6_3
  <=> r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f113,plain,
    ( spl6_6
  <=> ! [X0] :
        ( r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X0))
        | r2_waybel_0(sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f180,plain,
    ( r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
    | r2_waybel_0(sK0,sK1,k1_xboole_0)
    | ~ spl6_6 ),
    inference(superposition,[],[f114,f169])).

fof(f169,plain,(
    ! [X15] : k6_subset_1(X15,k1_xboole_0) = X15 ),
    inference(resolution,[],[f149,f85])).

fof(f149,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK5(X5,X6,X5),X6)
      | k6_subset_1(X5,X6) = X5 ) ),
    inference(global_subsumption,[],[f99,f146])).

fof(f146,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK5(X5,X6,X5),X6)
      | ~ r2_hidden(sK5(X5,X6,X5),X5)
      | k6_subset_1(X5,X6) = X5 ) ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK5(X5,X6,X5),X6)
      | ~ r2_hidden(sK5(X5,X6,X5),X5)
      | k6_subset_1(X5,X6) = X5
      | k6_subset_1(X5,X6) = X5 ) ),
    inference(resolution,[],[f54,f99])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X2)
      | k6_subset_1(X0,X1) = X2 ) ),
    inference(definition_unfolding,[],[f43,f39])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f99,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1,X0),X0)
      | k6_subset_1(X0,X1) = X0 ) ),
    inference(factoring,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k6_subset_1(X0,X1) = X2 ) ),
    inference(definition_unfolding,[],[f44,f39])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f114,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X0))
        | r2_waybel_0(sK0,sK1,X0) )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f115,plain,
    ( spl6_6
    | spl6_2
    | spl6_5
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f111,f74,f59,f79,f64,f113])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(sK1)
        | v2_struct_0(sK0)
        | r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X0))
        | r2_waybel_0(sK0,sK1,X0) )
    | ~ spl6_4 ),
    inference(resolution,[],[f31,f76])).

fof(f76,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_0)).

fof(f82,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f25,f79])).

fof(f25,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).

fof(f77,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f26,f74])).

fof(f26,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f72,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f27,f69])).

fof(f27,plain,(
    ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f67,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f28,f64])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f62,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f29,f59])).

fof(f29,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:55:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (31996)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (32020)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (32011)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (32021)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (32020)Refutation not found, incomplete strategy% (32020)------------------------------
% 0.21/0.52  % (32020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (32003)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (32020)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (32020)Memory used [KB]: 1663
% 0.21/0.52  % (32020)Time elapsed: 0.058 s
% 0.21/0.52  % (32020)------------------------------
% 0.21/0.52  % (32020)------------------------------
% 0.21/0.52  % (32021)Refutation not found, incomplete strategy% (32021)------------------------------
% 0.21/0.52  % (32021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (32021)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (32021)Memory used [KB]: 10746
% 0.21/0.52  % (32021)Time elapsed: 0.115 s
% 0.21/0.52  % (32021)------------------------------
% 0.21/0.52  % (32021)------------------------------
% 0.21/0.52  % (31999)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (32009)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (32008)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (32012)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (32016)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (32016)Refutation not found, incomplete strategy% (32016)------------------------------
% 0.21/0.53  % (32016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32016)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (32016)Memory used [KB]: 10618
% 0.21/0.53  % (32016)Time elapsed: 0.136 s
% 0.21/0.53  % (32016)------------------------------
% 0.21/0.53  % (32016)------------------------------
% 0.21/0.53  % (32014)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (32022)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (31997)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (32028)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (32002)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (32000)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (32001)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (31998)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (32023)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (32000)Refutation not found, incomplete strategy% (32000)------------------------------
% 0.21/0.54  % (32000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32000)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (32000)Memory used [KB]: 6268
% 0.21/0.54  % (32000)Time elapsed: 0.136 s
% 0.21/0.54  % (32000)------------------------------
% 0.21/0.54  % (32000)------------------------------
% 0.21/0.54  % (31998)Refutation not found, incomplete strategy% (31998)------------------------------
% 0.21/0.54  % (31998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31998)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31998)Memory used [KB]: 10618
% 0.21/0.54  % (31998)Time elapsed: 0.133 s
% 0.21/0.54  % (31998)------------------------------
% 0.21/0.54  % (31998)------------------------------
% 0.21/0.54  % (32008)Refutation not found, incomplete strategy% (32008)------------------------------
% 0.21/0.54  % (32008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32008)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (32008)Memory used [KB]: 10618
% 0.21/0.54  % (32008)Time elapsed: 0.134 s
% 0.21/0.54  % (32008)------------------------------
% 0.21/0.54  % (32008)------------------------------
% 0.21/0.54  % (32004)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (32013)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (32004)Refutation not found, incomplete strategy% (32004)------------------------------
% 0.21/0.54  % (32004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32004)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (32004)Memory used [KB]: 10618
% 0.21/0.54  % (32004)Time elapsed: 0.133 s
% 0.21/0.54  % (32004)------------------------------
% 0.21/0.54  % (32004)------------------------------
% 0.21/0.55  % (32019)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (32024)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (32019)Refutation not found, incomplete strategy% (32019)------------------------------
% 0.21/0.55  % (32019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32019)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (32019)Memory used [KB]: 10746
% 0.21/0.55  % (32019)Time elapsed: 0.137 s
% 0.21/0.55  % (32019)------------------------------
% 0.21/0.55  % (32019)------------------------------
% 0.21/0.55  % (32025)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (32026)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (32024)Refutation not found, incomplete strategy% (32024)------------------------------
% 0.21/0.55  % (32024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32005)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (32017)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (32006)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (32025)Refutation not found, incomplete strategy% (32025)------------------------------
% 0.21/0.55  % (32025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32025)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (32025)Memory used [KB]: 10746
% 0.21/0.55  % (32025)Time elapsed: 0.148 s
% 0.21/0.55  % (32025)------------------------------
% 0.21/0.55  % (32025)------------------------------
% 0.21/0.55  % (32024)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (32024)Memory used [KB]: 6268
% 0.21/0.55  % (32024)Time elapsed: 0.141 s
% 0.21/0.55  % (32024)------------------------------
% 0.21/0.55  % (32024)------------------------------
% 0.21/0.55  % (32027)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (32006)Refutation not found, incomplete strategy% (32006)------------------------------
% 0.21/0.55  % (32006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32006)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (32006)Memory used [KB]: 10618
% 0.21/0.55  % (32006)Time elapsed: 0.149 s
% 0.21/0.55  % (32006)------------------------------
% 0.21/0.55  % (32006)------------------------------
% 0.21/0.56  % (32018)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.66/0.57  % (32014)Refutation found. Thanks to Tanya!
% 1.66/0.57  % SZS status Theorem for theBenchmark
% 1.66/0.57  % SZS output start Proof for theBenchmark
% 1.66/0.57  fof(f492,plain,(
% 1.66/0.57    $false),
% 1.66/0.57    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f82,f115,f186,f486,f490])).
% 1.66/0.57  fof(f490,plain,(
% 1.66/0.57    ~spl6_19),
% 1.66/0.57    inference(avatar_contradiction_clause,[],[f487])).
% 1.66/0.57  fof(f487,plain,(
% 1.66/0.57    $false | ~spl6_19),
% 1.66/0.57    inference(resolution,[],[f485,f85])).
% 1.66/0.57  fof(f85,plain,(
% 1.66/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.66/0.57    inference(resolution,[],[f83,f41])).
% 1.66/0.57  fof(f41,plain,(
% 1.66/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.66/0.57    inference(cnf_transformation,[],[f22])).
% 1.66/0.57  fof(f22,plain,(
% 1.66/0.57    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.66/0.57    inference(ennf_transformation,[],[f7])).
% 1.66/0.57  fof(f7,axiom,(
% 1.66/0.57    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.66/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.66/0.57  fof(f83,plain,(
% 1.66/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.66/0.57    inference(resolution,[],[f40,f30])).
% 1.66/0.57  fof(f30,plain,(
% 1.66/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.66/0.57    inference(cnf_transformation,[],[f4])).
% 1.66/0.57  fof(f4,axiom,(
% 1.66/0.57    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.66/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.66/0.57  fof(f40,plain,(
% 1.66/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.66/0.57    inference(cnf_transformation,[],[f21])).
% 1.66/0.57  fof(f21,plain,(
% 1.66/0.57    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 1.66/0.57    inference(ennf_transformation,[],[f12])).
% 1.66/0.57  fof(f12,plain,(
% 1.66/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 1.66/0.57    inference(unused_predicate_definition_removal,[],[f5])).
% 1.66/0.57  fof(f5,axiom,(
% 1.66/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.66/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.66/0.57  fof(f485,plain,(
% 1.66/0.57    r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k1_xboole_0,sK4(u1_struct_0(sK1)))),k1_xboole_0) | ~spl6_19),
% 1.66/0.57    inference(avatar_component_clause,[],[f483])).
% 1.66/0.57  fof(f483,plain,(
% 1.66/0.57    spl6_19 <=> r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k1_xboole_0,sK4(u1_struct_0(sK1)))),k1_xboole_0)),
% 1.66/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.66/0.57  fof(f486,plain,(
% 1.66/0.57    ~spl6_1 | spl6_19 | spl6_2 | ~spl6_4 | spl6_5 | ~spl6_12),
% 1.66/0.57    inference(avatar_split_clause,[],[f481,f183,f79,f74,f64,f483,f59])).
% 1.66/0.57  fof(f59,plain,(
% 1.66/0.57    spl6_1 <=> l1_struct_0(sK0)),
% 1.66/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.66/0.57  fof(f64,plain,(
% 1.66/0.57    spl6_2 <=> v2_struct_0(sK0)),
% 1.66/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.66/0.57  fof(f74,plain,(
% 1.66/0.57    spl6_4 <=> l1_waybel_0(sK1,sK0)),
% 1.66/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.66/0.57  fof(f79,plain,(
% 1.66/0.57    spl6_5 <=> v2_struct_0(sK1)),
% 1.66/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.66/0.57  fof(f183,plain,(
% 1.66/0.57    spl6_12 <=> r2_waybel_0(sK0,sK1,k1_xboole_0)),
% 1.66/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.66/0.57  fof(f481,plain,(
% 1.66/0.57    v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0) | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k1_xboole_0,sK4(u1_struct_0(sK1)))),k1_xboole_0) | ~l1_struct_0(sK0) | ~spl6_12),
% 1.66/0.57    inference(resolution,[],[f187,f185])).
% 1.66/0.57  fof(f185,plain,(
% 1.66/0.57    r2_waybel_0(sK0,sK1,k1_xboole_0) | ~spl6_12),
% 1.66/0.57    inference(avatar_component_clause,[],[f183])).
% 1.66/0.57  fof(f187,plain,(
% 1.66/0.57    ( ! [X2,X0,X1] : (~r2_waybel_0(X0,X1,X2) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X0) | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,sK4(u1_struct_0(X1)))),X2) | ~l1_struct_0(X0)) )),
% 1.66/0.57    inference(resolution,[],[f36,f38])).
% 1.66/0.57  fof(f38,plain,(
% 1.66/0.57    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) )),
% 1.66/0.57    inference(cnf_transformation,[],[f2])).
% 1.66/0.57  fof(f2,axiom,(
% 1.66/0.57    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 1.66/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 1.66/0.57  fof(f36,plain,(
% 1.66/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X0) | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2) | ~r2_waybel_0(X0,X1,X2)) )),
% 1.66/0.57    inference(cnf_transformation,[],[f20])).
% 1.66/0.57  fof(f20,plain,(
% 1.66/0.57    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.66/0.57    inference(flattening,[],[f19])).
% 1.66/0.57  fof(f19,plain,(
% 1.66/0.57    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.66/0.57    inference(ennf_transformation,[],[f8])).
% 1.66/0.57  fof(f8,axiom,(
% 1.66/0.57    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 1.66/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).
% 1.66/0.57  fof(f186,plain,(
% 1.66/0.57    spl6_12 | spl6_3 | ~spl6_6),
% 1.66/0.57    inference(avatar_split_clause,[],[f180,f113,f69,f183])).
% 1.66/0.57  fof(f69,plain,(
% 1.66/0.57    spl6_3 <=> r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 1.66/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.66/0.57  fof(f113,plain,(
% 1.66/0.57    spl6_6 <=> ! [X0] : (r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X0)) | r2_waybel_0(sK0,sK1,X0))),
% 1.66/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.66/0.57  fof(f180,plain,(
% 1.66/0.57    r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) | r2_waybel_0(sK0,sK1,k1_xboole_0) | ~spl6_6),
% 1.66/0.57    inference(superposition,[],[f114,f169])).
% 1.66/0.57  fof(f169,plain,(
% 1.66/0.57    ( ! [X15] : (k6_subset_1(X15,k1_xboole_0) = X15) )),
% 1.66/0.57    inference(resolution,[],[f149,f85])).
% 1.66/0.57  fof(f149,plain,(
% 1.66/0.57    ( ! [X6,X5] : (r2_hidden(sK5(X5,X6,X5),X6) | k6_subset_1(X5,X6) = X5) )),
% 1.66/0.57    inference(global_subsumption,[],[f99,f146])).
% 1.66/0.57  fof(f146,plain,(
% 1.66/0.57    ( ! [X6,X5] : (r2_hidden(sK5(X5,X6,X5),X6) | ~r2_hidden(sK5(X5,X6,X5),X5) | k6_subset_1(X5,X6) = X5) )),
% 1.66/0.57    inference(duplicate_literal_removal,[],[f145])).
% 1.66/0.57  fof(f145,plain,(
% 1.66/0.57    ( ! [X6,X5] : (r2_hidden(sK5(X5,X6,X5),X6) | ~r2_hidden(sK5(X5,X6,X5),X5) | k6_subset_1(X5,X6) = X5 | k6_subset_1(X5,X6) = X5) )),
% 1.66/0.57    inference(resolution,[],[f54,f99])).
% 1.66/0.57  fof(f54,plain,(
% 1.66/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2) | k6_subset_1(X0,X1) = X2) )),
% 1.66/0.57    inference(definition_unfolding,[],[f43,f39])).
% 1.66/0.57  fof(f39,plain,(
% 1.66/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.66/0.57    inference(cnf_transformation,[],[f3])).
% 1.66/0.57  fof(f3,axiom,(
% 1.66/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.66/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.66/0.57  fof(f43,plain,(
% 1.66/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.66/0.57    inference(cnf_transformation,[],[f1])).
% 1.66/0.57  fof(f1,axiom,(
% 1.66/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.66/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.66/0.57  fof(f99,plain,(
% 1.66/0.57    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1,X0),X0) | k6_subset_1(X0,X1) = X0) )),
% 1.66/0.57    inference(factoring,[],[f53])).
% 1.66/0.57  fof(f53,plain,(
% 1.66/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2) | k6_subset_1(X0,X1) = X2) )),
% 1.66/0.57    inference(definition_unfolding,[],[f44,f39])).
% 1.66/0.57  fof(f44,plain,(
% 1.66/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.66/0.57    inference(cnf_transformation,[],[f1])).
% 1.66/0.57  fof(f114,plain,(
% 1.66/0.57    ( ! [X0] : (r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X0)) | r2_waybel_0(sK0,sK1,X0)) ) | ~spl6_6),
% 1.66/0.57    inference(avatar_component_clause,[],[f113])).
% 1.66/0.57  fof(f115,plain,(
% 1.66/0.57    spl6_6 | spl6_2 | spl6_5 | ~spl6_1 | ~spl6_4),
% 1.66/0.57    inference(avatar_split_clause,[],[f111,f74,f59,f79,f64,f113])).
% 1.66/0.57  fof(f111,plain,(
% 1.66/0.57    ( ! [X0] : (~l1_struct_0(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X0)) | r2_waybel_0(sK0,sK1,X0)) ) | ~spl6_4),
% 1.66/0.57    inference(resolution,[],[f31,f76])).
% 1.66/0.57  fof(f76,plain,(
% 1.66/0.57    l1_waybel_0(sK1,sK0) | ~spl6_4),
% 1.66/0.57    inference(avatar_component_clause,[],[f74])).
% 1.66/0.57  fof(f31,plain,(
% 1.66/0.57    ( ! [X2,X0,X1] : (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | v2_struct_0(X0) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | r2_waybel_0(X0,X1,X2)) )),
% 1.66/0.57    inference(cnf_transformation,[],[f18])).
% 1.66/0.57  fof(f18,plain,(
% 1.66/0.57    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.66/0.57    inference(flattening,[],[f17])).
% 1.66/0.57  fof(f17,plain,(
% 1.66/0.57    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.66/0.57    inference(ennf_transformation,[],[f9])).
% 1.66/0.57  fof(f9,axiom,(
% 1.66/0.57    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 1.66/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_0)).
% 1.66/0.57  fof(f82,plain,(
% 1.66/0.57    ~spl6_5),
% 1.66/0.57    inference(avatar_split_clause,[],[f25,f79])).
% 1.66/0.57  fof(f25,plain,(
% 1.66/0.57    ~v2_struct_0(sK1)),
% 1.66/0.57    inference(cnf_transformation,[],[f16])).
% 1.66/0.57  fof(f16,plain,(
% 1.66/0.57    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.66/0.57    inference(flattening,[],[f15])).
% 1.66/0.57  fof(f15,plain,(
% 1.66/0.57    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.66/0.57    inference(ennf_transformation,[],[f14])).
% 1.66/0.57  fof(f14,plain,(
% 1.66/0.57    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.66/0.57    inference(pure_predicate_removal,[],[f13])).
% 1.66/0.57  fof(f13,plain,(
% 1.66/0.57    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.66/0.57    inference(pure_predicate_removal,[],[f11])).
% 1.66/0.57  fof(f11,negated_conjecture,(
% 1.66/0.57    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.66/0.57    inference(negated_conjecture,[],[f10])).
% 1.66/0.57  fof(f10,conjecture,(
% 1.66/0.57    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.66/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).
% 1.66/0.57  fof(f77,plain,(
% 1.66/0.57    spl6_4),
% 1.66/0.57    inference(avatar_split_clause,[],[f26,f74])).
% 1.66/0.57  fof(f26,plain,(
% 1.66/0.57    l1_waybel_0(sK1,sK0)),
% 1.66/0.57    inference(cnf_transformation,[],[f16])).
% 1.66/0.57  fof(f72,plain,(
% 1.66/0.57    ~spl6_3),
% 1.66/0.57    inference(avatar_split_clause,[],[f27,f69])).
% 1.66/0.57  fof(f27,plain,(
% 1.66/0.57    ~r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 1.66/0.57    inference(cnf_transformation,[],[f16])).
% 1.66/0.57  fof(f67,plain,(
% 1.66/0.57    ~spl6_2),
% 1.66/0.57    inference(avatar_split_clause,[],[f28,f64])).
% 1.66/0.57  fof(f28,plain,(
% 1.66/0.57    ~v2_struct_0(sK0)),
% 1.66/0.57    inference(cnf_transformation,[],[f16])).
% 1.66/0.57  fof(f62,plain,(
% 1.66/0.57    spl6_1),
% 1.66/0.57    inference(avatar_split_clause,[],[f29,f59])).
% 1.66/0.57  fof(f29,plain,(
% 1.66/0.57    l1_struct_0(sK0)),
% 1.66/0.57    inference(cnf_transformation,[],[f16])).
% 1.66/0.57  % SZS output end Proof for theBenchmark
% 1.66/0.57  % (32014)------------------------------
% 1.66/0.57  % (32014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.57  % (32014)Termination reason: Refutation
% 1.66/0.57  
% 1.66/0.57  % (32014)Memory used [KB]: 11001
% 1.66/0.57  % (32014)Time elapsed: 0.157 s
% 1.66/0.57  % (32014)------------------------------
% 1.66/0.57  % (32014)------------------------------
% 1.66/0.57  % (31990)Success in time 0.205 s
%------------------------------------------------------------------------------
