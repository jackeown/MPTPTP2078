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
% DateTime   : Thu Dec  3 12:59:27 EST 2020

% Result     : Theorem 1.84s
% Output     : Refutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 241 expanded)
%              Number of leaves         :   24 (  89 expanded)
%              Depth                    :   20
%              Number of atoms          :  421 ( 991 expanded)
%              Number of equality atoms :  161 ( 406 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f415,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f76,f80,f84,f88,f203,f235,f250,f268,f333,f353,f388,f414])).

fof(f414,plain,
    ( spl5_26
    | ~ spl5_5
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f404,f201,f86,f233])).

fof(f233,plain,
    ( spl5_26
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f86,plain,
    ( spl5_5
  <=> m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f201,plain,
    ( spl5_22
  <=> ! [X1,X2] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

% (23436)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f404,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl5_5
    | ~ spl5_22 ),
    inference(resolution,[],[f390,f87])).

fof(f87,plain,
    ( m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f390,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) )
    | ~ spl5_22 ),
    inference(resolution,[],[f361,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

% (23425)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f361,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
        | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )
    | ~ spl5_22 ),
    inference(resolution,[],[f354,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f354,plain,
    ( ! [X2,X0,X1] : ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
    | ~ spl5_22 ),
    inference(resolution,[],[f202,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f202,plain,
    ( ! [X2,X1] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X1,X2))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f201])).

fof(f388,plain,
    ( spl5_4
    | spl5_3
    | spl5_2
    | ~ spl5_5
    | ~ spl5_19
    | spl5_1 ),
    inference(avatar_split_clause,[],[f381,f70,f186,f86,f74,f78,f82])).

fof(f82,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f78,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f74,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f186,plain,
    ( spl5_19
  <=> sK3 = k2_mcart_1(k1_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f70,plain,
    ( spl5_1
  <=> sK3 = k6_mcart_1(sK0,sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f381,plain,
    ( sK3 != k2_mcart_1(k1_mcart_1(sK4))
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl5_1 ),
    inference(superposition,[],[f71,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f51,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f71,plain,
    ( sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f353,plain,
    ( spl5_26
    | ~ spl5_5
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f346,f198,f86,f233])).

fof(f198,plain,
    ( spl5_21
  <=> ! [X3,X4] : ~ r2_hidden(sK4,k2_zfmisc_1(X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

% (23437)Refutation not found, incomplete strategy% (23437)------------------------------
% (23437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23437)Termination reason: Refutation not found, incomplete strategy

% (23437)Memory used [KB]: 1663
% (23437)Time elapsed: 0.192 s
% (23437)------------------------------
% (23437)------------------------------
fof(f346,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl5_5
    | ~ spl5_21 ),
    inference(resolution,[],[f340,f87])).

fof(f340,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) )
    | ~ spl5_21 ),
    inference(resolution,[],[f334,f37])).

fof(f334,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k2_zfmisc_1(X0,X1))
        | ~ m1_subset_1(sK4,k2_zfmisc_1(X0,X1)) )
    | ~ spl5_21 ),
    inference(resolution,[],[f199,f41])).

fof(f199,plain,
    ( ! [X4,X3] : ~ r2_hidden(sK4,k2_zfmisc_1(X3,X4))
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f198])).

fof(f333,plain,
    ( spl5_26
    | ~ spl5_5
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f326,f189,f86,f233])).

fof(f189,plain,
    ( spl5_20
  <=> ! [X0] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f326,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl5_5
    | ~ spl5_20 ),
    inference(resolution,[],[f317,f87])).

fof(f317,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1) )
    | ~ spl5_20 ),
    inference(resolution,[],[f304,f37])).

fof(f304,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))
        | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1)) )
    | ~ spl5_20 ),
    inference(resolution,[],[f285,f41])).

fof(f285,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))
    | ~ spl5_20 ),
    inference(resolution,[],[f190,f44])).

fof(f190,plain,
    ( ! [X0] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f189])).

fof(f268,plain,
    ( spl5_26
    | ~ spl5_5
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f263,f180,f86,f233])).

fof(f180,plain,
    ( spl5_17
  <=> ! [X1] : ~ r2_hidden(sK4,k2_zfmisc_1(X1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f263,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl5_5
    | ~ spl5_17 ),
    inference(resolution,[],[f259,f87])).

fof(f259,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(X0,sK2))
        | k1_xboole_0 = k2_zfmisc_1(X0,sK2) )
    | ~ spl5_17 ),
    inference(resolution,[],[f255,f37])).

fof(f255,plain,
    ( ! [X0] :
        ( v1_xboole_0(k2_zfmisc_1(X0,sK2))
        | ~ m1_subset_1(sK4,k2_zfmisc_1(X0,sK2)) )
    | ~ spl5_17 ),
    inference(resolution,[],[f181,f41])).

fof(f181,plain,
    ( ! [X1] : ~ r2_hidden(sK4,k2_zfmisc_1(X1,sK2))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f180])).

fof(f250,plain,
    ( spl5_4
    | spl5_3
    | spl5_2
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f244,f233,f74,f78,f82])).

fof(f244,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl5_26 ),
    inference(trivial_inequality_removal,[],[f240])).

fof(f240,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl5_26 ),
    inference(superposition,[],[f60,f234])).

fof(f234,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f233])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f46,f43])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f235,plain,
    ( spl5_26
    | ~ spl5_5
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f228,f177,f86,f233])).

fof(f177,plain,
    ( spl5_16
  <=> ! [X3,X2] : ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f228,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl5_5
    | ~ spl5_16 ),
    inference(resolution,[],[f225,f87])).

fof(f225,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1) )
    | ~ spl5_16 ),
    inference(resolution,[],[f222,f37])).

fof(f222,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))
        | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1)) )
    | ~ spl5_16 ),
    inference(resolution,[],[f178,f41])).

fof(f178,plain,
    ( ! [X2,X3] : ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X3))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f177])).

fof(f203,plain,
    ( spl5_16
    | spl5_17
    | spl5_19
    | spl5_21
    | spl5_22
    | spl5_20 ),
    inference(avatar_split_clause,[],[f196,f189,f201,f198,f186,f180,f177])).

% (23436)Refutation not found, incomplete strategy% (23436)------------------------------
% (23436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23436)Termination reason: Refutation not found, incomplete strategy

% (23436)Memory used [KB]: 10746
% (23436)Time elapsed: 0.193 s
% (23436)------------------------------
% (23436)------------------------------
fof(f196,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))
      | ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(sK4,k2_zfmisc_1(X3,X4))
      | sK3 = k2_mcart_1(k1_mcart_1(sK4))
      | ~ r2_hidden(sK4,k2_zfmisc_1(X5,sK2))
      | ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X6),X7)) ) ),
    inference(equality_resolution,[],[f194])).

fof(f194,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sK4 != X0
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X0,k2_zfmisc_1(X4,X5))
      | sK3 = k2_mcart_1(k1_mcart_1(X0))
      | ~ r2_hidden(X0,k2_zfmisc_1(X6,sK2))
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X7),X8)) ) ),
    inference(resolution,[],[f159,f38])).

fof(f38,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f159,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ v1_relat_1(X4)
      | sK4 != X0
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X0,X4)
      | sK3 = k2_mcart_1(k1_mcart_1(X0))
      | ~ r2_hidden(X0,k2_zfmisc_1(X5,sK2))
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X6),X7)) ) ),
    inference(resolution,[],[f155,f38])).

fof(f155,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X1)
      | sK3 = k2_mcart_1(k1_mcart_1(X0))
      | sK4 != X0
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X2,sK1))
      | ~ r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,X3)
      | ~ v1_relat_1(X3)
      | ~ r2_hidden(X0,k2_zfmisc_1(X4,sK2))
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X5),X6)) ) ),
    inference(resolution,[],[f143,f44])).

fof(f143,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k1_mcart_1(X1),k2_zfmisc_1(sK0,X3))
      | ~ r2_hidden(k1_mcart_1(X1),X0)
      | sK3 = k2_mcart_1(k1_mcart_1(X1))
      | sK4 != X1
      | ~ r2_hidden(k1_mcart_1(X1),k2_zfmisc_1(X2,sK1))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,X4)
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(X1,k2_zfmisc_1(X5,sK2)) ) ),
    inference(resolution,[],[f141,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f141,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_mcart_1(X0),sK2)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k1_mcart_1(X0),X1)
      | sK3 = k2_mcart_1(k1_mcart_1(X0))
      | sK4 != X0
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X2,sK1))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X3))
      | ~ r2_hidden(X0,X4)
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f128,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f128,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sK4 != k4_tarski(X0,X2)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,X1)
      | k2_mcart_1(X0) = sK3
      | ~ r2_hidden(X2,sK2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X3,sK1))
      | ~ r2_hidden(X0,k2_zfmisc_1(sK0,X4)) ) ),
    inference(resolution,[],[f118,f44])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k1_mcart_1(X0),sK0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1)
      | sK4 != k4_tarski(X0,X2)
      | k2_mcart_1(X0) = sK3
      | ~ r2_hidden(X2,sK2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X3,sK1)) ) ),
    inference(resolution,[],[f117,f45])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k2_mcart_1(X0),sK1)
      | k2_mcart_1(X0) = sK3
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X2)
      | k4_tarski(X0,X1) != sK4
      | ~ r2_hidden(k1_mcart_1(X0),sK0)
      | ~ r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f116,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,sK2)
      | sK4 != k4_tarski(X1,X0)
      | sK3 = k2_mcart_1(X1)
      | ~ r2_hidden(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k2_mcart_1(X1),sK1)
      | ~ r2_hidden(k1_mcart_1(X1),sK0) ) ),
    inference(resolution,[],[f115,f40])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k1_mcart_1(X0),sK0)
      | ~ m1_subset_1(X1,sK2)
      | k4_tarski(X0,X1) != sK4
      | k2_mcart_1(X0) = sK3
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k2_mcart_1(X0),sK1) ) ),
    inference(resolution,[],[f114,f40])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k2_mcart_1(X0),sK1)
      | k2_mcart_1(X0) = sK3
      | ~ m1_subset_1(X1,sK2)
      | k4_tarski(X0,X1) != sK4
      | ~ m1_subset_1(k1_mcart_1(X0),sK0)
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f55,f39])).

fof(f55,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X6
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f32,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f32,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X6
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK3 = X6
                | k3_mcart_1(X5,X6,X7) != sK4
                | ~ m1_subset_1(X7,sK2) )
            | ~ m1_subset_1(X6,sK1) )
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k6_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X6
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK3 = X6
                  | k3_mcart_1(X5,X6,X7) != sK4
                  | ~ m1_subset_1(X7,sK2) )
              | ~ m1_subset_1(X6,sK1) )
          | ~ m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X6 ) ) ) )
         => ( k6_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X6 ) ) ) )
       => ( k6_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_mcart_1)).

fof(f88,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f56,f86])).

fof(f56,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f31,f43])).

fof(f31,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f84,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f33,f82])).

fof(f33,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f34,f78])).

fof(f34,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f35,f74])).

fof(f35,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f36,f70])).

fof(f36,plain,(
    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n005.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:34:02 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.55  % (23420)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (23426)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (23419)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.56  % (23417)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.57  % (23443)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.57  % (23422)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.57  % (23427)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.57  % (23421)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.57  % (23435)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.58  % (23439)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.60/0.59  % (23431)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.60/0.59  % (23416)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.60/0.59  % (23439)Refutation not found, incomplete strategy% (23439)------------------------------
% 1.60/0.59  % (23439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.59  % (23439)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.59  
% 1.60/0.59  % (23439)Memory used [KB]: 1791
% 1.60/0.59  % (23439)Time elapsed: 0.116 s
% 1.60/0.59  % (23439)------------------------------
% 1.60/0.59  % (23439)------------------------------
% 1.84/0.60  % (23423)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.84/0.60  % (23416)Refutation not found, incomplete strategy% (23416)------------------------------
% 1.84/0.60  % (23416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.60  % (23416)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.60  
% 1.84/0.60  % (23416)Memory used [KB]: 1791
% 1.84/0.60  % (23416)Time elapsed: 0.131 s
% 1.84/0.60  % (23416)------------------------------
% 1.84/0.60  % (23416)------------------------------
% 1.84/0.60  % (23438)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.84/0.60  % (23430)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.84/0.60  % (23445)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.84/0.61  % (23444)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.84/0.61  % (23424)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.84/0.61  % (23418)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.84/0.61  % (23437)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.84/0.61  % (23435)Refutation found. Thanks to Tanya!
% 1.84/0.61  % SZS status Theorem for theBenchmark
% 1.84/0.61  % SZS output start Proof for theBenchmark
% 1.84/0.61  fof(f415,plain,(
% 1.84/0.61    $false),
% 1.84/0.61    inference(avatar_sat_refutation,[],[f72,f76,f80,f84,f88,f203,f235,f250,f268,f333,f353,f388,f414])).
% 1.84/0.61  fof(f414,plain,(
% 1.84/0.61    spl5_26 | ~spl5_5 | ~spl5_22),
% 1.84/0.61    inference(avatar_split_clause,[],[f404,f201,f86,f233])).
% 1.84/0.61  fof(f233,plain,(
% 1.84/0.61    spl5_26 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.84/0.61  fof(f86,plain,(
% 1.84/0.61    spl5_5 <=> m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.84/0.61  fof(f201,plain,(
% 1.84/0.61    spl5_22 <=> ! [X1,X2] : ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X1,X2))),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 1.84/0.61  % (23436)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.84/0.61  fof(f404,plain,(
% 1.84/0.61    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | (~spl5_5 | ~spl5_22)),
% 1.84/0.61    inference(resolution,[],[f390,f87])).
% 1.84/0.61  fof(f87,plain,(
% 1.84/0.61    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl5_5),
% 1.84/0.61    inference(avatar_component_clause,[],[f86])).
% 1.84/0.61  fof(f390,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) | ~spl5_22),
% 1.84/0.61    inference(resolution,[],[f361,f37])).
% 1.84/0.61  fof(f37,plain,(
% 1.84/0.61    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.84/0.61    inference(cnf_transformation,[],[f17])).
% 1.84/0.61  % (23425)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.84/0.61  fof(f17,plain,(
% 1.84/0.61    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.84/0.61    inference(ennf_transformation,[],[f1])).
% 1.84/0.61  fof(f1,axiom,(
% 1.84/0.61    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.84/0.61  fof(f361,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) ) | ~spl5_22),
% 1.84/0.61    inference(resolution,[],[f354,f41])).
% 1.84/0.61  fof(f41,plain,(
% 1.84/0.61    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f22])).
% 1.84/0.61  fof(f22,plain,(
% 1.84/0.61    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.84/0.61    inference(flattening,[],[f21])).
% 1.84/0.61  fof(f21,plain,(
% 1.84/0.61    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.84/0.61    inference(ennf_transformation,[],[f3])).
% 1.84/0.61  fof(f3,axiom,(
% 1.84/0.61    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.84/0.61  fof(f354,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) ) | ~spl5_22),
% 1.84/0.61    inference(resolution,[],[f202,f44])).
% 1.84/0.61  fof(f44,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.84/0.61    inference(cnf_transformation,[],[f23])).
% 1.84/0.61  fof(f23,plain,(
% 1.84/0.61    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.84/0.61    inference(ennf_transformation,[],[f9])).
% 1.84/0.61  fof(f9,axiom,(
% 1.84/0.61    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.84/0.61  fof(f202,plain,(
% 1.84/0.61    ( ! [X2,X1] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X1,X2))) ) | ~spl5_22),
% 1.84/0.61    inference(avatar_component_clause,[],[f201])).
% 1.84/0.61  fof(f388,plain,(
% 1.84/0.61    spl5_4 | spl5_3 | spl5_2 | ~spl5_5 | ~spl5_19 | spl5_1),
% 1.84/0.61    inference(avatar_split_clause,[],[f381,f70,f186,f86,f74,f78,f82])).
% 1.84/0.61  fof(f82,plain,(
% 1.84/0.61    spl5_4 <=> k1_xboole_0 = sK0),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.84/0.61  fof(f78,plain,(
% 1.84/0.61    spl5_3 <=> k1_xboole_0 = sK1),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.84/0.61  fof(f74,plain,(
% 1.84/0.61    spl5_2 <=> k1_xboole_0 = sK2),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.84/0.61  fof(f186,plain,(
% 1.84/0.61    spl5_19 <=> sK3 = k2_mcart_1(k1_mcart_1(sK4))),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.84/0.61  fof(f70,plain,(
% 1.84/0.61    spl5_1 <=> sK3 = k6_mcart_1(sK0,sK1,sK2,sK4)),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.84/0.61  fof(f381,plain,(
% 1.84/0.61    sK3 != k2_mcart_1(k1_mcart_1(sK4)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl5_1),
% 1.84/0.61    inference(superposition,[],[f71,f62])).
% 1.84/0.61  fof(f62,plain,(
% 1.84/0.61    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.84/0.61    inference(definition_unfolding,[],[f51,f43])).
% 1.84/0.61  fof(f43,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f6])).
% 1.84/0.61  fof(f6,axiom,(
% 1.84/0.61    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.84/0.61  fof(f51,plain,(
% 1.84/0.61    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.84/0.61    inference(cnf_transformation,[],[f24])).
% 1.84/0.61  fof(f24,plain,(
% 1.84/0.61    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.84/0.61    inference(ennf_transformation,[],[f12])).
% 1.84/0.61  fof(f12,axiom,(
% 1.84/0.61    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.84/0.61  fof(f71,plain,(
% 1.84/0.61    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) | spl5_1),
% 1.84/0.61    inference(avatar_component_clause,[],[f70])).
% 1.84/0.61  fof(f353,plain,(
% 1.84/0.61    spl5_26 | ~spl5_5 | ~spl5_21),
% 1.84/0.61    inference(avatar_split_clause,[],[f346,f198,f86,f233])).
% 1.84/0.61  fof(f198,plain,(
% 1.84/0.61    spl5_21 <=> ! [X3,X4] : ~r2_hidden(sK4,k2_zfmisc_1(X3,X4))),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 1.84/0.61  % (23437)Refutation not found, incomplete strategy% (23437)------------------------------
% 1.84/0.61  % (23437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.61  % (23437)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.61  
% 1.84/0.61  % (23437)Memory used [KB]: 1663
% 1.84/0.61  % (23437)Time elapsed: 0.192 s
% 1.84/0.61  % (23437)------------------------------
% 1.84/0.61  % (23437)------------------------------
% 1.84/0.61  fof(f346,plain,(
% 1.84/0.61    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | (~spl5_5 | ~spl5_21)),
% 1.84/0.61    inference(resolution,[],[f340,f87])).
% 1.84/0.61  fof(f340,plain,(
% 1.84/0.61    ( ! [X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) ) | ~spl5_21),
% 1.84/0.61    inference(resolution,[],[f334,f37])).
% 1.84/0.61  fof(f334,plain,(
% 1.84/0.61    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~m1_subset_1(sK4,k2_zfmisc_1(X0,X1))) ) | ~spl5_21),
% 1.84/0.61    inference(resolution,[],[f199,f41])).
% 1.84/0.61  fof(f199,plain,(
% 1.84/0.61    ( ! [X4,X3] : (~r2_hidden(sK4,k2_zfmisc_1(X3,X4))) ) | ~spl5_21),
% 1.84/0.61    inference(avatar_component_clause,[],[f198])).
% 1.84/0.61  fof(f333,plain,(
% 1.84/0.61    spl5_26 | ~spl5_5 | ~spl5_20),
% 1.84/0.61    inference(avatar_split_clause,[],[f326,f189,f86,f233])).
% 1.84/0.61  fof(f189,plain,(
% 1.84/0.61    spl5_20 <=> ! [X0] : ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.84/0.61  fof(f326,plain,(
% 1.84/0.61    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | (~spl5_5 | ~spl5_20)),
% 1.84/0.61    inference(resolution,[],[f317,f87])).
% 1.84/0.61  fof(f317,plain,(
% 1.84/0.61    ( ! [X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1)) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1)) ) | ~spl5_20),
% 1.84/0.61    inference(resolution,[],[f304,f37])).
% 1.84/0.61  fof(f304,plain,(
% 1.84/0.61    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))) ) | ~spl5_20),
% 1.84/0.61    inference(resolution,[],[f285,f41])).
% 1.84/0.61  fof(f285,plain,(
% 1.84/0.61    ( ! [X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))) ) | ~spl5_20),
% 1.84/0.61    inference(resolution,[],[f190,f44])).
% 1.84/0.61  fof(f190,plain,(
% 1.84/0.61    ( ! [X0] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))) ) | ~spl5_20),
% 1.84/0.61    inference(avatar_component_clause,[],[f189])).
% 1.84/0.61  fof(f268,plain,(
% 1.84/0.61    spl5_26 | ~spl5_5 | ~spl5_17),
% 1.84/0.61    inference(avatar_split_clause,[],[f263,f180,f86,f233])).
% 1.84/0.61  fof(f180,plain,(
% 1.84/0.61    spl5_17 <=> ! [X1] : ~r2_hidden(sK4,k2_zfmisc_1(X1,sK2))),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.84/0.61  fof(f263,plain,(
% 1.84/0.61    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | (~spl5_5 | ~spl5_17)),
% 1.84/0.61    inference(resolution,[],[f259,f87])).
% 1.84/0.61  fof(f259,plain,(
% 1.84/0.61    ( ! [X0] : (~m1_subset_1(sK4,k2_zfmisc_1(X0,sK2)) | k1_xboole_0 = k2_zfmisc_1(X0,sK2)) ) | ~spl5_17),
% 1.84/0.61    inference(resolution,[],[f255,f37])).
% 1.84/0.61  fof(f255,plain,(
% 1.84/0.61    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(X0,sK2)) | ~m1_subset_1(sK4,k2_zfmisc_1(X0,sK2))) ) | ~spl5_17),
% 1.84/0.61    inference(resolution,[],[f181,f41])).
% 1.84/0.61  fof(f181,plain,(
% 1.84/0.61    ( ! [X1] : (~r2_hidden(sK4,k2_zfmisc_1(X1,sK2))) ) | ~spl5_17),
% 1.84/0.61    inference(avatar_component_clause,[],[f180])).
% 1.84/0.61  fof(f250,plain,(
% 1.84/0.61    spl5_4 | spl5_3 | spl5_2 | ~spl5_26),
% 1.84/0.61    inference(avatar_split_clause,[],[f244,f233,f74,f78,f82])).
% 1.84/0.61  fof(f244,plain,(
% 1.84/0.61    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl5_26),
% 1.84/0.61    inference(trivial_inequality_removal,[],[f240])).
% 1.84/0.61  fof(f240,plain,(
% 1.84/0.61    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl5_26),
% 1.84/0.61    inference(superposition,[],[f60,f234])).
% 1.84/0.61  fof(f234,plain,(
% 1.84/0.61    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl5_26),
% 1.84/0.61    inference(avatar_component_clause,[],[f233])).
% 1.84/0.61  fof(f60,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.84/0.61    inference(definition_unfolding,[],[f46,f43])).
% 1.84/0.61  fof(f46,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.84/0.61    inference(cnf_transformation,[],[f30])).
% 1.84/0.61  fof(f30,plain,(
% 1.84/0.61    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.84/0.61    inference(flattening,[],[f29])).
% 1.84/0.61  fof(f29,plain,(
% 1.84/0.61    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | (k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.84/0.61    inference(nnf_transformation,[],[f11])).
% 1.84/0.61  fof(f11,axiom,(
% 1.84/0.61    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).
% 1.84/0.61  fof(f235,plain,(
% 1.84/0.61    spl5_26 | ~spl5_5 | ~spl5_16),
% 1.84/0.61    inference(avatar_split_clause,[],[f228,f177,f86,f233])).
% 1.84/0.61  fof(f177,plain,(
% 1.84/0.61    spl5_16 <=> ! [X3,X2] : ~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X3))),
% 1.84/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.84/0.61  fof(f228,plain,(
% 1.84/0.61    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | (~spl5_5 | ~spl5_16)),
% 1.84/0.61    inference(resolution,[],[f225,f87])).
% 1.84/0.61  fof(f225,plain,(
% 1.84/0.61    ( ! [X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1)) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1)) ) | ~spl5_16),
% 1.84/0.61    inference(resolution,[],[f222,f37])).
% 1.84/0.61  fof(f222,plain,(
% 1.84/0.61    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))) ) | ~spl5_16),
% 1.84/0.61    inference(resolution,[],[f178,f41])).
% 1.84/0.61  fof(f178,plain,(
% 1.84/0.61    ( ! [X2,X3] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X3))) ) | ~spl5_16),
% 1.84/0.61    inference(avatar_component_clause,[],[f177])).
% 1.84/0.61  fof(f203,plain,(
% 1.84/0.61    spl5_16 | spl5_17 | spl5_19 | spl5_21 | spl5_22 | spl5_20),
% 1.84/0.61    inference(avatar_split_clause,[],[f196,f189,f201,f198,f186,f180,f177])).
% 1.84/0.61  % (23436)Refutation not found, incomplete strategy% (23436)------------------------------
% 1.84/0.61  % (23436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.61  % (23436)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.61  
% 1.84/0.61  % (23436)Memory used [KB]: 10746
% 1.84/0.61  % (23436)Time elapsed: 0.193 s
% 1.84/0.61  % (23436)------------------------------
% 1.84/0.61  % (23436)------------------------------
% 1.84/0.61  fof(f196,plain,(
% 1.84/0.61    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1)) | ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X1,X2)) | ~r2_hidden(sK4,k2_zfmisc_1(X3,X4)) | sK3 = k2_mcart_1(k1_mcart_1(sK4)) | ~r2_hidden(sK4,k2_zfmisc_1(X5,sK2)) | ~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X6),X7))) )),
% 1.84/0.61    inference(equality_resolution,[],[f194])).
% 1.84/0.61  fof(f194,plain,(
% 1.84/0.61    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sK4 != X0 | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X0,k2_zfmisc_1(X4,X5)) | sK3 = k2_mcart_1(k1_mcart_1(X0)) | ~r2_hidden(X0,k2_zfmisc_1(X6,sK2)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X7),X8))) )),
% 1.84/0.61    inference(resolution,[],[f159,f38])).
% 1.84/0.61  fof(f38,plain,(
% 1.84/0.61    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.84/0.61    inference(cnf_transformation,[],[f4])).
% 1.84/0.61  fof(f4,axiom,(
% 1.84/0.61    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.84/0.61  fof(f159,plain,(
% 1.84/0.61    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~v1_relat_1(X4) | sK4 != X0 | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X0,X4) | sK3 = k2_mcart_1(k1_mcart_1(X0)) | ~r2_hidden(X0,k2_zfmisc_1(X5,sK2)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X6),X7))) )),
% 1.84/0.61    inference(resolution,[],[f155,f38])).
% 1.84/0.61  fof(f155,plain,(
% 1.84/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~v1_relat_1(X1) | sK3 = k2_mcart_1(k1_mcart_1(X0)) | sK4 != X0 | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X2,sK1)) | ~r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,X3) | ~v1_relat_1(X3) | ~r2_hidden(X0,k2_zfmisc_1(X4,sK2)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X5),X6))) )),
% 1.84/0.61    inference(resolution,[],[f143,f44])).
% 1.84/0.61  fof(f143,plain,(
% 1.84/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(k1_mcart_1(X1),k2_zfmisc_1(sK0,X3)) | ~r2_hidden(k1_mcart_1(X1),X0) | sK3 = k2_mcart_1(k1_mcart_1(X1)) | sK4 != X1 | ~r2_hidden(k1_mcart_1(X1),k2_zfmisc_1(X2,sK1)) | ~v1_relat_1(X0) | ~r2_hidden(X1,X4) | ~v1_relat_1(X4) | ~r2_hidden(X1,k2_zfmisc_1(X5,sK2))) )),
% 1.84/0.61    inference(resolution,[],[f141,f45])).
% 1.84/0.61  fof(f45,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.84/0.61    inference(cnf_transformation,[],[f23])).
% 1.84/0.61  fof(f141,plain,(
% 1.84/0.61    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(k2_mcart_1(X0),sK2) | ~v1_relat_1(X1) | ~r2_hidden(k1_mcart_1(X0),X1) | sK3 = k2_mcart_1(k1_mcart_1(X0)) | sK4 != X0 | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X2,sK1)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X3)) | ~r2_hidden(X0,X4) | ~v1_relat_1(X4)) )),
% 1.84/0.61    inference(superposition,[],[f128,f39])).
% 1.84/0.61  fof(f39,plain,(
% 1.84/0.61    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f19])).
% 1.84/0.61  fof(f19,plain,(
% 1.84/0.61    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 1.84/0.61    inference(flattening,[],[f18])).
% 1.84/0.61  fof(f18,plain,(
% 1.84/0.61    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 1.84/0.61    inference(ennf_transformation,[],[f10])).
% 1.84/0.61  fof(f10,axiom,(
% 1.84/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).
% 1.84/0.61  fof(f128,plain,(
% 1.84/0.61    ( ! [X4,X2,X0,X3,X1] : (sK4 != k4_tarski(X0,X2) | ~v1_relat_1(X1) | ~r2_hidden(X0,X1) | k2_mcart_1(X0) = sK3 | ~r2_hidden(X2,sK2) | ~r2_hidden(X0,k2_zfmisc_1(X3,sK1)) | ~r2_hidden(X0,k2_zfmisc_1(sK0,X4))) )),
% 1.84/0.61    inference(resolution,[],[f118,f44])).
% 1.84/0.61  fof(f118,plain,(
% 1.84/0.61    ( ! [X2,X0,X3,X1] : (~r2_hidden(k1_mcart_1(X0),sK0) | ~r2_hidden(X0,X1) | ~v1_relat_1(X1) | sK4 != k4_tarski(X0,X2) | k2_mcart_1(X0) = sK3 | ~r2_hidden(X2,sK2) | ~r2_hidden(X0,k2_zfmisc_1(X3,sK1))) )),
% 1.84/0.61    inference(resolution,[],[f117,f45])).
% 1.84/0.61  fof(f117,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (~r2_hidden(k2_mcart_1(X0),sK1) | k2_mcart_1(X0) = sK3 | ~r2_hidden(X0,X2) | ~v1_relat_1(X2) | k4_tarski(X0,X1) != sK4 | ~r2_hidden(k1_mcart_1(X0),sK0) | ~r2_hidden(X1,sK2)) )),
% 1.84/0.61    inference(resolution,[],[f116,f40])).
% 1.84/0.61  fof(f40,plain,(
% 1.84/0.61    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f20])).
% 1.84/0.61  fof(f20,plain,(
% 1.84/0.61    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.84/0.61    inference(ennf_transformation,[],[f2])).
% 1.84/0.61  fof(f2,axiom,(
% 1.84/0.61    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.84/0.61  fof(f116,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X0,sK2) | sK4 != k4_tarski(X1,X0) | sK3 = k2_mcart_1(X1) | ~r2_hidden(X1,X2) | ~v1_relat_1(X2) | ~r2_hidden(k2_mcart_1(X1),sK1) | ~r2_hidden(k1_mcart_1(X1),sK0)) )),
% 1.84/0.61    inference(resolution,[],[f115,f40])).
% 1.84/0.61  fof(f115,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(k1_mcart_1(X0),sK0) | ~m1_subset_1(X1,sK2) | k4_tarski(X0,X1) != sK4 | k2_mcart_1(X0) = sK3 | ~r2_hidden(X0,X2) | ~v1_relat_1(X2) | ~r2_hidden(k2_mcart_1(X0),sK1)) )),
% 1.84/0.61    inference(resolution,[],[f114,f40])).
% 1.84/0.61  fof(f114,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(k2_mcart_1(X0),sK1) | k2_mcart_1(X0) = sK3 | ~m1_subset_1(X1,sK2) | k4_tarski(X0,X1) != sK4 | ~m1_subset_1(k1_mcart_1(X0),sK0) | ~r2_hidden(X0,X2) | ~v1_relat_1(X2)) )),
% 1.84/0.61    inference(superposition,[],[f55,f39])).
% 1.84/0.61  fof(f55,plain,(
% 1.84/0.61    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X6 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 1.84/0.61    inference(definition_unfolding,[],[f32,f42])).
% 1.84/0.61  fof(f42,plain,(
% 1.84/0.61    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f5])).
% 1.84/0.61  fof(f5,axiom,(
% 1.84/0.61    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.84/0.61  fof(f32,plain,(
% 1.84/0.61    ( ! [X6,X7,X5] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 1.84/0.61    inference(cnf_transformation,[],[f28])).
% 1.84/0.61  fof(f28,plain,(
% 1.84/0.61    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.84/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f27])).
% 1.84/0.61  fof(f27,plain,(
% 1.84/0.61    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 1.84/0.61    introduced(choice_axiom,[])).
% 1.84/0.61  fof(f16,plain,(
% 1.84/0.61    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.84/0.61    inference(flattening,[],[f15])).
% 1.84/0.61  fof(f15,plain,(
% 1.84/0.61    ? [X0,X1,X2,X3,X4] : (((k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X6 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.84/0.61    inference(ennf_transformation,[],[f14])).
% 1.84/0.61  fof(f14,negated_conjecture,(
% 1.84/0.61    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.84/0.61    inference(negated_conjecture,[],[f13])).
% 1.84/0.61  fof(f13,conjecture,(
% 1.84/0.61    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.84/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_mcart_1)).
% 1.84/0.61  fof(f88,plain,(
% 1.84/0.61    spl5_5),
% 1.84/0.61    inference(avatar_split_clause,[],[f56,f86])).
% 1.84/0.61  fof(f56,plain,(
% 1.84/0.61    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.84/0.61    inference(definition_unfolding,[],[f31,f43])).
% 1.84/0.61  fof(f31,plain,(
% 1.84/0.61    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.84/0.61    inference(cnf_transformation,[],[f28])).
% 1.84/0.61  fof(f84,plain,(
% 1.84/0.61    ~spl5_4),
% 1.84/0.61    inference(avatar_split_clause,[],[f33,f82])).
% 1.84/0.61  fof(f33,plain,(
% 1.84/0.61    k1_xboole_0 != sK0),
% 1.84/0.61    inference(cnf_transformation,[],[f28])).
% 1.84/0.61  fof(f80,plain,(
% 1.84/0.61    ~spl5_3),
% 1.84/0.61    inference(avatar_split_clause,[],[f34,f78])).
% 1.84/0.61  fof(f34,plain,(
% 1.84/0.61    k1_xboole_0 != sK1),
% 1.84/0.61    inference(cnf_transformation,[],[f28])).
% 1.84/0.61  fof(f76,plain,(
% 1.84/0.61    ~spl5_2),
% 1.84/0.61    inference(avatar_split_clause,[],[f35,f74])).
% 1.84/0.61  fof(f35,plain,(
% 1.84/0.61    k1_xboole_0 != sK2),
% 1.84/0.61    inference(cnf_transformation,[],[f28])).
% 1.84/0.61  fof(f72,plain,(
% 1.84/0.61    ~spl5_1),
% 1.84/0.61    inference(avatar_split_clause,[],[f36,f70])).
% 1.84/0.61  fof(f36,plain,(
% 1.84/0.61    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)),
% 1.84/0.61    inference(cnf_transformation,[],[f28])).
% 1.84/0.61  % SZS output end Proof for theBenchmark
% 1.84/0.61  % (23435)------------------------------
% 1.84/0.61  % (23435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.61  % (23435)Termination reason: Refutation
% 1.84/0.61  
% 1.84/0.61  % (23435)Memory used [KB]: 11001
% 1.84/0.61  % (23435)Time elapsed: 0.174 s
% 1.84/0.61  % (23435)------------------------------
% 1.84/0.61  % (23435)------------------------------
% 1.84/0.61  % (23434)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.84/0.62  % (23442)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.84/0.62  % (23429)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.84/0.62  % (23428)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.84/0.62  % (23438)Refutation not found, incomplete strategy% (23438)------------------------------
% 1.84/0.62  % (23438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.62  % (23438)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.62  
% 1.84/0.62  % (23438)Memory used [KB]: 10746
% 1.84/0.62  % (23438)Time elapsed: 0.182 s
% 1.84/0.62  % (23438)------------------------------
% 1.84/0.62  % (23438)------------------------------
% 1.84/0.62  % (23415)Success in time 0.256 s
%------------------------------------------------------------------------------
