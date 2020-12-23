%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 158 expanded)
%              Number of leaves         :   25 (  65 expanded)
%              Depth                    :    7
%              Number of atoms          :  265 ( 510 expanded)
%              Number of equality atoms :   24 (  34 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f594,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f86,f91,f96,f102,f112,f114,f134,f151,f170,f177,f195,f593])).

fof(f593,plain,
    ( ~ spl3_18
    | ~ spl3_7
    | ~ spl3_6
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f591,f193,f88,f93,f172])).

fof(f172,plain,
    ( spl3_18
  <=> r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f93,plain,
    ( spl3_7
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f88,plain,
    ( spl3_6
  <=> r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f193,plain,
    ( spl3_20
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
        | ~ r2_hidden(X0,k6_domain_1(u1_struct_0(sK0),sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f591,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ spl3_6
    | ~ spl3_20 ),
    inference(resolution,[],[f194,f90])).

fof(f90,plain,
    ( r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f194,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f193])).

fof(f195,plain,
    ( spl3_5
    | spl3_20
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f191,f167,f78,f73,f68,f63,f193,f83])).

fof(f83,plain,
    ( spl3_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f63,plain,
    ( spl3_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f68,plain,
    ( spl3_2
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f73,plain,
    ( spl3_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f78,plain,
    ( spl3_4
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f167,plain,
    ( spl3_17
  <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f191,plain,
    ( ! [X0] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r2_hidden(X0,k6_domain_1(u1_struct_0(sK0),sK1))
        | ~ r2_hidden(X0,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) )
    | ~ spl3_17 ),
    inference(resolution,[],[f37,f169])).

fof(f169,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f167])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X1,k1_orders_2(X0,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k1_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
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
              ( ~ r2_hidden(X1,k1_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( r2_hidden(X1,k1_orders_2(X0,X2))
                  & r2_hidden(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_orders_2)).

fof(f177,plain,
    ( spl3_18
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f164,f148,f172])).

fof(f148,plain,
    ( spl3_15
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_enumset1(sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f164,plain,
    ( r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ spl3_15 ),
    inference(superposition,[],[f56,f150])).

fof(f150,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_enumset1(sK1,sK1,sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f148])).

fof(f56,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k1_enumset1(X0,X1,X4)) ),
    inference(equality_resolution,[],[f55])).

% (18297)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f55,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f170,plain,
    ( spl3_17
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f160,f148,f131,f167])).

fof(f131,plain,
    ( spl3_12
  <=> m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f160,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(backward_demodulation,[],[f133,f150])).

fof(f133,plain,
    ( m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f131])).

fof(f151,plain,
    ( spl3_15
    | spl3_10
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f145,f93,f109,f148])).

fof(f109,plain,
    ( spl3_10
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f145,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_enumset1(sK1,sK1,sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f54,f95])).

fof(f95,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1) ) ),
    inference(definition_unfolding,[],[f42,f52])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f39])).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

% (18302)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (18289)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (18289)Refutation not found, incomplete strategy% (18289)------------------------------
% (18289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18289)Termination reason: Refutation not found, incomplete strategy

% (18289)Memory used [KB]: 10618
% (18289)Time elapsed: 0.118 s
% (18289)------------------------------
% (18289)------------------------------
% (18278)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f134,plain,
    ( spl3_12
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f124,f105,f131])).

fof(f105,plain,
    ( spl3_9
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f124,plain,
    ( m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_9 ),
    inference(resolution,[],[f53,f107])).

fof(f107,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f105])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1)) ) ),
    inference(definition_unfolding,[],[f40,f52])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f114,plain,
    ( spl3_5
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f113,f109,f99,f83])).

fof(f99,plain,
    ( spl3_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f113,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_10 ),
    inference(resolution,[],[f111,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f111,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f112,plain,
    ( spl3_9
    | spl3_10
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f103,f93,f109,f105])).

fof(f103,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl3_7 ),
    inference(resolution,[],[f41,f95])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f102,plain,
    ( spl3_8
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f97,f63,f99])).

fof(f97,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f36,f65])).

fof(f65,plain,
    ( l1_orders_2(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f96,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f28,f93])).

fof(f28,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_orders_2)).

fof(f91,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f29,f88])).

fof(f29,plain,(
    r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f86,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f30,f83])).

fof(f30,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f81,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f31,f78])).

fof(f31,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f32,f73])).

fof(f32,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f71,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f33,f68])).

fof(f33,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f66,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f34,f63])).

fof(f34,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:10:03 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (18286)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.49  % (18294)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (18286)Refutation not found, incomplete strategy% (18286)------------------------------
% 0.21/0.51  % (18286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (18286)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (18286)Memory used [KB]: 10746
% 0.21/0.51  % (18286)Time elapsed: 0.087 s
% 0.21/0.51  % (18286)------------------------------
% 0.21/0.51  % (18286)------------------------------
% 0.21/0.51  % (18282)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (18299)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (18294)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f594,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f86,f91,f96,f102,f112,f114,f134,f151,f170,f177,f195,f593])).
% 0.21/0.52  fof(f593,plain,(
% 0.21/0.52    ~spl3_18 | ~spl3_7 | ~spl3_6 | ~spl3_20),
% 0.21/0.52    inference(avatar_split_clause,[],[f591,f193,f88,f93,f172])).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    spl3_18 <=> r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    spl3_7 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    spl3_6 <=> r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.52  fof(f193,plain,(
% 0.21/0.52    spl3_20 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~r2_hidden(X0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.52  fof(f591,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1)) | (~spl3_6 | ~spl3_20)),
% 0.21/0.52    inference(resolution,[],[f194,f90])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~spl3_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f88])).
% 0.21/0.52  fof(f194,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k6_domain_1(u1_struct_0(sK0),sK1))) ) | ~spl3_20),
% 0.21/0.52    inference(avatar_component_clause,[],[f193])).
% 0.21/0.52  fof(f195,plain,(
% 0.21/0.52    spl3_5 | spl3_20 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_17),
% 0.21/0.52    inference(avatar_split_clause,[],[f191,f167,f78,f73,f68,f63,f193,f83])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    spl3_5 <=> v2_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    spl3_1 <=> l1_orders_2(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    spl3_2 <=> v5_orders_2(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    spl3_3 <=> v4_orders_2(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    spl3_4 <=> v3_orders_2(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    spl3_17 <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    ( ! [X0] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X0,k6_domain_1(u1_struct_0(sK0),sK1)) | ~r2_hidden(X0,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))) ) | ~spl3_17),
% 0.21/0.52    inference(resolution,[],[f37,f169])).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f167])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_hidden(X1,X2) | ~r2_hidden(X1,k1_orders_2(X0,X2))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k1_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_orders_2)).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    spl3_18 | ~spl3_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f164,f148,f172])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    spl3_15 <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_enumset1(sK1,sK1,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1)) | ~spl3_15),
% 0.21/0.52    inference(superposition,[],[f56,f150])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    k6_domain_1(u1_struct_0(sK0),sK1) = k1_enumset1(sK1,sK1,sK1) | ~spl3_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f148])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_enumset1(X0,X1,X4))) )),
% 0.21/0.52    inference(equality_resolution,[],[f55])).
% 0.21/0.52  % (18297)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k1_enumset1(X0,X1,X4) != X3) )),
% 0.21/0.52    inference(equality_resolution,[],[f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    spl3_17 | ~spl3_12 | ~spl3_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f160,f148,f131,f167])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    spl3_12 <=> m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_12 | ~spl3_15)),
% 0.21/0.52    inference(backward_demodulation,[],[f133,f150])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f131])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    spl3_15 | spl3_10 | ~spl3_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f145,f93,f109,f148])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    spl3_10 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    v1_xboole_0(u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),sK1) = k1_enumset1(sK1,sK1,sK1) | ~spl3_7),
% 0.21/0.52    inference(resolution,[],[f54,f95])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f93])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f42,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f35,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.52  % (18302)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (18289)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (18289)Refutation not found, incomplete strategy% (18289)------------------------------
% 0.21/0.53  % (18289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (18289)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (18289)Memory used [KB]: 10618
% 0.21/0.53  % (18289)Time elapsed: 0.118 s
% 0.21/0.53  % (18289)------------------------------
% 0.21/0.53  % (18289)------------------------------
% 0.21/0.53  % (18278)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    spl3_12 | ~spl3_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f124,f105,f131])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    spl3_9 <=> r2_hidden(sK1,u1_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_9),
% 0.21/0.53    inference(resolution,[],[f53,f107])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    r2_hidden(sK1,u1_struct_0(sK0)) | ~spl3_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f105])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f40,f52])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    spl3_5 | ~spl3_8 | ~spl3_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f113,f109,f99,f83])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    spl3_8 <=> l1_struct_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl3_10),
% 0.21/0.53    inference(resolution,[],[f111,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    v1_xboole_0(u1_struct_0(sK0)) | ~spl3_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f109])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    spl3_9 | spl3_10 | ~spl3_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f103,f93,f109,f105])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK1,u1_struct_0(sK0)) | ~spl3_7),
% 0.21/0.53    inference(resolution,[],[f41,f95])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    spl3_8 | ~spl3_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f97,f63,f99])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    l1_struct_0(sK0) | ~spl3_1),
% 0.21/0.53    inference(resolution,[],[f36,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    l1_orders_2(sK0) | ~spl3_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f63])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    spl3_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f28,f93])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.21/0.53    inference(negated_conjecture,[],[f11])).
% 0.21/0.53  fof(f11,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_orders_2)).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    spl3_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f29,f88])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ~spl3_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f30,f83])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ~v2_struct_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    spl3_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f31,f78])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    v3_orders_2(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    spl3_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f32,f73])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    v4_orders_2(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    spl3_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f33,f68])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    v5_orders_2(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    spl3_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f34,f63])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    l1_orders_2(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (18294)------------------------------
% 0.21/0.53  % (18294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (18294)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (18294)Memory used [KB]: 11129
% 0.21/0.53  % (18294)Time elapsed: 0.100 s
% 0.21/0.53  % (18294)------------------------------
% 0.21/0.53  % (18294)------------------------------
% 0.21/0.54  % (18277)Success in time 0.167 s
%------------------------------------------------------------------------------
