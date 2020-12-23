%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  227 ( 466 expanded)
%              Number of leaves         :   49 ( 208 expanded)
%              Depth                    :   15
%              Number of atoms          :  991 (1836 expanded)
%              Number of equality atoms :   95 ( 212 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f384,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f101,f107,f112,f119,f124,f132,f151,f202,f215,f220,f226,f230,f243,f251,f260,f267,f282,f287,f297,f304,f309,f313,f326,f328,f361,f374,f383])).

% (2154)Refutation not found, incomplete strategy% (2154)------------------------------
% (2154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2157)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% (2156)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% (2148)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% (2161)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% (2155)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (2149)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% (2158)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% (2148)Refutation not found, incomplete strategy% (2148)------------------------------
% (2148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2148)Termination reason: Refutation not found, incomplete strategy

% (2148)Memory used [KB]: 1663
% (2148)Time elapsed: 0.090 s
% (2148)------------------------------
% (2148)------------------------------
% (2168)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% (2153)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f383,plain,
    ( ~ spl5_5
    | ~ spl5_9
    | ~ spl5_24
    | ~ spl5_41 ),
    inference(avatar_contradiction_clause,[],[f382])).

fof(f382,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_24
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f381,f255])).

fof(f255,plain,
    ( m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl5_24
  <=> m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f381,plain,
    ( ~ m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_41 ),
    inference(forward_demodulation,[],[f380,f123])).

fof(f123,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl5_9
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f380,plain,
    ( ~ m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl5_5
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f379,f100])).

fof(f100,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl5_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f379,plain,
    ( ~ m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl5_41 ),
    inference(resolution,[],[f373,f76])).

fof(f76,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(f373,plain,
    ( r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK1(k2_orders_2(sK0,k2_struct_0(sK0))))
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f371])).

fof(f371,plain,
    ( spl5_41
  <=> r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK1(k2_orders_2(sK0,k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f374,plain,
    ( spl5_41
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f367,f359,f257,f240,f371])).

fof(f240,plain,
    ( spl5_22
  <=> sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f257,plain,
    ( spl5_25
  <=> r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f359,plain,
    ( spl5_39
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f367,plain,
    ( r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK1(k2_orders_2(sK0,k2_struct_0(sK0))))
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_39 ),
    inference(subsumption_resolution,[],[f366,f258])).

fof(f258,plain,
    ( r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f257])).

fof(f366,plain,
    ( r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK1(k2_orders_2(sK0,k2_struct_0(sK0))))
    | ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))
    | ~ spl5_22
    | ~ spl5_39 ),
    inference(superposition,[],[f360,f242])).

fof(f242,plain,
    ( sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f240])).

fof(f360,plain,
    ( ! [X0] :
        ( r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0))))
        | ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) )
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f359])).

fof(f361,plain,
    ( spl5_39
    | ~ spl5_30
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f339,f307,f294,f359])).

fof(f294,plain,
    ( spl5_30
  <=> r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f307,plain,
    ( spl5_32
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
        | ~ r2_hidden(X0,k2_struct_0(sK0))
        | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f339,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0)))) )
    | ~ spl5_30
    | ~ spl5_32 ),
    inference(resolution,[],[f308,f296])).

fof(f296,plain,
    ( r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f294])).

fof(f308,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_struct_0(sK0))
        | ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
        | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),X0) )
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f307])).

fof(f328,plain,
    ( ~ spl5_33
    | spl5_34 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | ~ spl5_33
    | spl5_34 ),
    inference(unit_resulting_resolution,[],[f312,f320,f60])).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f320,plain,
    ( k1_xboole_0 != k2_struct_0(sK0)
    | spl5_34 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl5_34
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f312,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_struct_0(sK0))
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl5_33
  <=> ! [X0] : ~ r2_hidden(X0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f326,plain,
    ( k2_struct_0(sK0) != k2_orders_2(sK0,k1_xboole_0)
    | k1_xboole_0 != k2_struct_0(sK0)
    | k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f313,plain,
    ( spl5_33
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f305,f301,f311])).

fof(f301,plain,
    ( spl5_31
  <=> sP4(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f305,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_struct_0(sK0))
    | ~ spl5_31 ),
    inference(resolution,[],[f303,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ sP4(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(general_splitting,[],[f69,f74_D])).

fof(f74,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | sP4(X1) ) ),
    inference(cnf_transformation,[],[f74_D])).

fof(f74_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ v1_xboole_0(X2)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) )
    <=> ~ sP4(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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

fof(f303,plain,
    ( sP4(k2_struct_0(sK0))
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f301])).

fof(f309,plain,
    ( spl5_32
    | ~ spl5_10
    | ~ spl5_17
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f262,f249,f212,f129,f307])).

fof(f129,plain,
    ( spl5_10
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f212,plain,
    ( spl5_17
  <=> k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f249,plain,
    ( spl5_23
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
        | r2_orders_2(sK0,sK3(X2,sK0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f262,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
        | ~ r2_hidden(X0,k2_struct_0(sK0))
        | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),X0) )
    | ~ spl5_10
    | ~ spl5_17
    | ~ spl5_23 ),
    inference(forward_demodulation,[],[f261,f214])).

fof(f214,plain,
    ( k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f212])).

fof(f261,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_struct_0(sK0))
        | ~ r2_hidden(X1,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
        | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),X0) )
    | ~ spl5_10
    | ~ spl5_23 ),
    inference(resolution,[],[f250,f131])).

fof(f131,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f129])).

fof(f250,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
        | r2_orders_2(sK0,sK3(X2,sK0,X1),X0) )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f249])).

fof(f304,plain,
    ( spl5_31
    | ~ spl5_10
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f299,f285,f129,f301])).

fof(f285,plain,
    ( spl5_29
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | sP4(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f299,plain,
    ( sP4(k2_struct_0(sK0))
    | ~ spl5_10
    | ~ spl5_29 ),
    inference(resolution,[],[f286,f131])).

fof(f286,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | sP4(X0) )
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f285])).

fof(f297,plain,
    ( spl5_30
    | ~ spl5_10
    | ~ spl5_17
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f292,f280,f257,f240,f212,f129,f294])).

fof(f280,plain,
    ( spl5_28
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | r2_hidden(sK3(X1,sK0,X0),k2_struct_0(sK0))
        | ~ r2_hidden(X1,a_2_1_orders_2(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f292,plain,
    ( r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ spl5_10
    | ~ spl5_17
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f291,f258])).

fof(f291,plain,
    ( ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))
    | r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ spl5_10
    | ~ spl5_17
    | ~ spl5_22
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f290,f214])).

fof(f290,plain,
    ( r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0)))
    | ~ spl5_10
    | ~ spl5_22
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f289,f131])).

fof(f289,plain,
    ( r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0)))
    | ~ spl5_22
    | ~ spl5_28 ),
    inference(superposition,[],[f281,f242])).

fof(f281,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X1,sK0,X0),k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(X1,a_2_1_orders_2(sK0,X0)) )
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f280])).

fof(f287,plain,
    ( spl5_29
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f283,f276,f285])).

fof(f276,plain,
    ( spl5_27
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f283,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | sP4(X0) )
    | ~ spl5_27 ),
    inference(resolution,[],[f278,f74])).

fof(f278,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f276])).

fof(f282,plain,
    ( spl5_27
    | spl5_28
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f231,f224,f280,f276])).

fof(f224,plain,
    ( spl5_19
  <=> ! [X1,X0] :
        ( m1_subset_1(sK3(X0,sK0,X1),k2_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f231,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(X1,a_2_1_orders_2(sK0,X0))
        | v1_xboole_0(k2_struct_0(sK0))
        | r2_hidden(sK3(X1,sK0,X0),k2_struct_0(sK0)) )
    | ~ spl5_19 ),
    inference(resolution,[],[f225,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f225,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK3(X0,sK0,X1),k2_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1)) )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f224])).

fof(f267,plain,
    ( spl5_7
    | spl5_25 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | spl5_7
    | spl5_25 ),
    inference(subsumption_resolution,[],[f264,f111])).

fof(f111,plain,
    ( k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl5_7
  <=> k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f264,plain,
    ( k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0))
    | spl5_25 ),
    inference(resolution,[],[f259,f60])).

fof(f259,plain,
    ( ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))
    | spl5_25 ),
    inference(avatar_component_clause,[],[f257])).

fof(f260,plain,
    ( spl5_24
    | ~ spl5_25
    | ~ spl5_10
    | ~ spl5_17
    | ~ spl5_19
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f247,f240,f224,f212,f129,f257,f253])).

fof(f247,plain,
    ( ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))
    | m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ spl5_10
    | ~ spl5_17
    | ~ spl5_19
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f246,f214])).

fof(f246,plain,
    ( m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0)))
    | ~ spl5_10
    | ~ spl5_19
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f245,f131])).

fof(f245,plain,
    ( m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0)))
    | ~ spl5_19
    | ~ spl5_22 ),
    inference(superposition,[],[f225,f242])).

fof(f251,plain,
    ( spl5_23
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f210,f121,f98,f93,f88,f83,f78,f249])).

fof(f78,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f83,plain,
    ( spl5_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f88,plain,
    ( spl5_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f93,plain,
    ( spl5_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f210,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
        | r2_orders_2(sK0,sK3(X2,sK0,X1),X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f209,f123])).

fof(f209,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK3(X2,sK0,X1),X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f208,f80])).

fof(f80,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f208,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK3(X2,sK0,X1),X0)
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f207,f85])).

fof(f85,plain,
    ( v3_orders_2(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f207,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK3(X2,sK0,X1),X0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f206,f90])).

fof(f90,plain,
    ( v4_orders_2(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f206,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK3(X2,sK0,X1),X0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f205,f100])).

fof(f205,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | r2_orders_2(sK0,sK3(X2,sK0,X1),X0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f203,f95])).

fof(f95,plain,
    ( v5_orders_2(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f203,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ r2_hidden(X6,X2)
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | r2_orders_2(X1,sK3(X0,X1,X2),X6)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f64,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f64,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_orders_2(X1,sK3(X0,X1,X2),X6)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,X3,sK2(X1,X2,X3))
                & r2_hidden(sK2(X1,X2,X3),X2)
                & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,sK3(X0,X1,X2),X6)
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK3(X0,X1,X2) = X0
            & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f41,f43,f42])).

fof(f42,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK2(X1,X2,X3))
        & r2_hidden(sK2(X1,X2,X3),X2)
        & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X5,X6)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,sK3(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK3(X0,X1,X2) = X0
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X5,X6)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r2_orders_2(X1,X3,X4)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X3,X4) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(f243,plain,
    ( spl5_22
    | spl5_7
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f234,f228,f109,f240])).

fof(f228,plain,
    ( spl5_20
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | sK3(X0,sK0,k2_struct_0(sK0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f234,plain,
    ( sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))
    | spl5_7
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f232,f111])).

fof(f232,plain,
    ( sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))
    | k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0))
    | ~ spl5_20 ),
    inference(resolution,[],[f229,f60])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | sK3(X0,sK0,k2_struct_0(sK0)) = X0 )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f228])).

fof(f230,plain,
    ( spl5_20
    | ~ spl5_10
    | ~ spl5_17
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f222,f218,f212,f129,f228])).

fof(f218,plain,
    ( spl5_18
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | sK3(X0,sK0,X1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f222,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | sK3(X0,sK0,k2_struct_0(sK0)) = X0 )
    | ~ spl5_10
    | ~ spl5_17
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f221,f214])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
        | sK3(X0,sK0,k2_struct_0(sK0)) = X0 )
    | ~ spl5_10
    | ~ spl5_18 ),
    inference(resolution,[],[f219,f131])).

% (2144)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f219,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | sK3(X0,sK0,X1) = X0 )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f218])).

fof(f226,plain,
    ( spl5_19
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f185,f121,f98,f93,f88,f83,f78,f224])).

fof(f185,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK3(X0,sK0,X1),k2_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f184,f123])).

fof(f184,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f183,f123])).

fof(f183,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f182,f80])).

fof(f182,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f181,f85])).

fof(f181,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f180,f90])).

fof(f180,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f179,f100])).

fof(f179,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f62,f95])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f220,plain,
    ( spl5_18
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f169,f121,f98,f93,f88,f83,f78,f218])).

fof(f169,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | sK3(X0,sK0,X1) = X0 )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f168,f123])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK3(X0,sK0,X1) = X0 )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f167,f80])).

fof(f167,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK3(X0,sK0,X1) = X0
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f166,f85])).

fof(f166,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK3(X0,sK0,X1) = X0
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f165,f90])).

fof(f165,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK3(X0,sK0,X1) = X0
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f164,f100])).

fof(f164,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | sK3(X0,sK0,X1) = X0
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f63,f95])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | sK3(X0,X1,X2) = X0
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f215,plain,
    ( spl5_17
    | ~ spl5_10
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f204,f200,f129,f212])).

fof(f200,plain,
    ( spl5_16
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f204,plain,
    ( k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0))
    | ~ spl5_10
    | ~ spl5_16 ),
    inference(resolution,[],[f201,f131])).

fof(f201,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f200])).

fof(f202,plain,
    ( spl5_16
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f161,f121,f98,f93,f88,f83,f78,f200])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f160,f123])).

fof(f160,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f159,f80])).

fof(f159,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f158,f85])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f157,f90])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f156,f100])).

fof(f156,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f59,f95])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

fof(f151,plain,
    ( spl5_12
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f146,f121,f116,f98,f93,f88,f83,f78,f148])).

fof(f148,plain,
    ( spl5_12
  <=> k2_struct_0(sK0) = k2_orders_2(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f116,plain,
    ( spl5_8
  <=> k1_xboole_0 = k1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f146,plain,
    ( k2_struct_0(sK0) = k2_orders_2(sK0,k1_xboole_0)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f145,f123])).

fof(f145,plain,
    ( u1_struct_0(sK0) = k2_orders_2(sK0,k1_xboole_0)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f144,f118])).

fof(f118,plain,
    ( k1_xboole_0 = k1_struct_0(sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f116])).

fof(f144,plain,
    ( u1_struct_0(sK0) = k2_orders_2(sK0,k1_struct_0(sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f143,f80])).

fof(f143,plain,
    ( u1_struct_0(sK0) = k2_orders_2(sK0,k1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f142,f85])).

fof(f142,plain,
    ( u1_struct_0(sK0) = k2_orders_2(sK0,k1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f141,f90])).

fof(f141,plain,
    ( u1_struct_0(sK0) = k2_orders_2(sK0,k1_struct_0(sK0))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f140,f100])).

fof(f140,plain,
    ( ~ l1_orders_2(sK0)
    | u1_struct_0(sK0) = k2_orders_2(sK0,k1_struct_0(sK0))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f58,f95])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_orders_2)).

fof(f132,plain,
    ( spl5_10
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f127,f121,f104,f129])).

fof(f104,plain,
    ( spl5_6
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f127,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f126,f106])).

fof(f106,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f126,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | ~ spl5_9 ),
    inference(superposition,[],[f53,f123])).

% (2150)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
fof(f53,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f124,plain,
    ( spl5_9
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f114,f104,f121])).

fof(f114,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl5_6 ),
    inference(resolution,[],[f52,f106])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f119,plain,
    ( spl5_8
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f113,f104,f116])).

fof(f113,plain,
    ( k1_xboole_0 = k1_struct_0(sK0)
    | ~ spl5_6 ),
    inference(resolution,[],[f51,f106])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k1_xboole_0 = k1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

fof(f112,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f50,f109])).

fof(f50,plain,(
    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0))
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).

fof(f107,plain,
    ( spl5_6
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f102,f98,f104])).

fof(f102,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f54,f100])).

fof(f54,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f101,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f49,f98])).

fof(f49,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f96,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f48,f93])).

fof(f48,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f91,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f47,f88])).

fof(f47,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f86,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f46,f83])).

fof(f46,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f81,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f45,f78])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:32:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (2143)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (2154)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (2151)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (2146)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (2170)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (2142)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (2143)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f384,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f101,f107,f112,f119,f124,f132,f151,f202,f215,f220,f226,f230,f243,f251,f260,f267,f282,f287,f297,f304,f309,f313,f326,f328,f361,f374,f383])).
% 0.21/0.51  % (2154)Refutation not found, incomplete strategy% (2154)------------------------------
% 0.21/0.51  % (2154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2157)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (2156)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (2148)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (2161)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (2155)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (2149)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (2158)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (2148)Refutation not found, incomplete strategy% (2148)------------------------------
% 0.21/0.52  % (2148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2148)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (2148)Memory used [KB]: 1663
% 0.21/0.52  % (2148)Time elapsed: 0.090 s
% 0.21/0.52  % (2148)------------------------------
% 0.21/0.52  % (2148)------------------------------
% 0.21/0.52  % (2168)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (2153)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  fof(f383,plain,(
% 0.21/0.52    ~spl5_5 | ~spl5_9 | ~spl5_24 | ~spl5_41),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f382])).
% 0.21/0.52  fof(f382,plain,(
% 0.21/0.52    $false | (~spl5_5 | ~spl5_9 | ~spl5_24 | ~spl5_41)),
% 0.21/0.52    inference(subsumption_resolution,[],[f381,f255])).
% 0.21/0.52  fof(f255,plain,(
% 0.21/0.52    m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~spl5_24),
% 0.21/0.52    inference(avatar_component_clause,[],[f253])).
% 0.21/0.52  fof(f253,plain,(
% 0.21/0.52    spl5_24 <=> m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.52  fof(f381,plain,(
% 0.21/0.52    ~m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | (~spl5_5 | ~spl5_9 | ~spl5_41)),
% 0.21/0.52    inference(forward_demodulation,[],[f380,f123])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl5_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f121])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    spl5_9 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.52  fof(f380,plain,(
% 0.21/0.52    ~m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | (~spl5_5 | ~spl5_41)),
% 0.21/0.52    inference(subsumption_resolution,[],[f379,f100])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    l1_orders_2(sK0) | ~spl5_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f98])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    spl5_5 <=> l1_orders_2(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.52  fof(f379,plain,(
% 0.21/0.52    ~m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~spl5_41),
% 0.21/0.52    inference(resolution,[],[f373,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(flattening,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).
% 0.21/0.52  fof(f373,plain,(
% 0.21/0.52    r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK1(k2_orders_2(sK0,k2_struct_0(sK0)))) | ~spl5_41),
% 0.21/0.52    inference(avatar_component_clause,[],[f371])).
% 0.21/0.52  fof(f371,plain,(
% 0.21/0.52    spl5_41 <=> r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK1(k2_orders_2(sK0,k2_struct_0(sK0))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 0.21/0.52  fof(f374,plain,(
% 0.21/0.52    spl5_41 | ~spl5_22 | ~spl5_25 | ~spl5_39),
% 0.21/0.52    inference(avatar_split_clause,[],[f367,f359,f257,f240,f371])).
% 0.21/0.52  fof(f240,plain,(
% 0.21/0.52    spl5_22 <=> sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.52  fof(f257,plain,(
% 0.21/0.52    spl5_25 <=> r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.52  fof(f359,plain,(
% 0.21/0.52    spl5_39 <=> ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0)))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 0.21/0.52  fof(f367,plain,(
% 0.21/0.52    r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK1(k2_orders_2(sK0,k2_struct_0(sK0)))) | (~spl5_22 | ~spl5_25 | ~spl5_39)),
% 0.21/0.52    inference(subsumption_resolution,[],[f366,f258])).
% 0.21/0.52  fof(f258,plain,(
% 0.21/0.52    r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) | ~spl5_25),
% 0.21/0.52    inference(avatar_component_clause,[],[f257])).
% 0.21/0.52  fof(f366,plain,(
% 0.21/0.52    r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK1(k2_orders_2(sK0,k2_struct_0(sK0)))) | ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) | (~spl5_22 | ~spl5_39)),
% 0.21/0.52    inference(superposition,[],[f360,f242])).
% 0.21/0.52  fof(f242,plain,(
% 0.21/0.52    sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)) | ~spl5_22),
% 0.21/0.52    inference(avatar_component_clause,[],[f240])).
% 0.21/0.52  fof(f360,plain,(
% 0.21/0.52    ( ! [X0] : (r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0)))) | ~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))) ) | ~spl5_39),
% 0.21/0.52    inference(avatar_component_clause,[],[f359])).
% 0.21/0.52  fof(f361,plain,(
% 0.21/0.52    spl5_39 | ~spl5_30 | ~spl5_32),
% 0.21/0.52    inference(avatar_split_clause,[],[f339,f307,f294,f359])).
% 0.21/0.52  fof(f294,plain,(
% 0.21/0.52    spl5_30 <=> r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.21/0.52  fof(f307,plain,(
% 0.21/0.52    spl5_32 <=> ! [X1,X0] : (~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | ~r2_hidden(X0,k2_struct_0(sK0)) | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 0.21/0.52  fof(f339,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0))))) ) | (~spl5_30 | ~spl5_32)),
% 0.21/0.52    inference(resolution,[],[f308,f296])).
% 0.21/0.52  fof(f296,plain,(
% 0.21/0.52    r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~spl5_30),
% 0.21/0.52    inference(avatar_component_clause,[],[f294])).
% 0.21/0.52  fof(f308,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k2_struct_0(sK0)) | ~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),X0)) ) | ~spl5_32),
% 0.21/0.52    inference(avatar_component_clause,[],[f307])).
% 0.21/0.52  fof(f328,plain,(
% 0.21/0.52    ~spl5_33 | spl5_34),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f327])).
% 0.21/0.52  fof(f327,plain,(
% 0.21/0.52    $false | (~spl5_33 | spl5_34)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f312,f320,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.52  fof(f320,plain,(
% 0.21/0.52    k1_xboole_0 != k2_struct_0(sK0) | spl5_34),
% 0.21/0.52    inference(avatar_component_clause,[],[f319])).
% 0.21/0.52  fof(f319,plain,(
% 0.21/0.52    spl5_34 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 0.21/0.52  fof(f312,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k2_struct_0(sK0))) ) | ~spl5_33),
% 0.21/0.52    inference(avatar_component_clause,[],[f311])).
% 0.21/0.52  fof(f311,plain,(
% 0.21/0.52    spl5_33 <=> ! [X0] : ~r2_hidden(X0,k2_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.21/0.52  fof(f326,plain,(
% 0.21/0.52    k2_struct_0(sK0) != k2_orders_2(sK0,k1_xboole_0) | k1_xboole_0 != k2_struct_0(sK0) | k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0))),
% 0.21/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.52  fof(f313,plain,(
% 0.21/0.52    spl5_33 | ~spl5_31),
% 0.21/0.52    inference(avatar_split_clause,[],[f305,f301,f311])).
% 0.21/0.52  fof(f301,plain,(
% 0.21/0.52    spl5_31 <=> sP4(k2_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.21/0.52  fof(f305,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k2_struct_0(sK0))) ) | ~spl5_31),
% 0.21/0.52    inference(resolution,[],[f303,f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~sP4(X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(general_splitting,[],[f69,f74_D])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X2,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | sP4(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f74_D])).
% 0.21/0.52  fof(f74_D,plain,(
% 0.21/0.52    ( ! [X1] : (( ! [X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2))) ) <=> ~sP4(X1)) )),
% 0.21/0.52    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.52  fof(f303,plain,(
% 0.21/0.52    sP4(k2_struct_0(sK0)) | ~spl5_31),
% 0.21/0.52    inference(avatar_component_clause,[],[f301])).
% 0.21/0.52  fof(f309,plain,(
% 0.21/0.52    spl5_32 | ~spl5_10 | ~spl5_17 | ~spl5_23),
% 0.21/0.52    inference(avatar_split_clause,[],[f262,f249,f212,f129,f307])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    spl5_10 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.52  fof(f212,plain,(
% 0.21/0.52    spl5_17 <=> k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.52  fof(f249,plain,(
% 0.21/0.52    spl5_23 <=> ! [X1,X0,X2] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,X1) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | r2_orders_2(sK0,sK3(X2,sK0,X1),X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.52  fof(f262,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | ~r2_hidden(X0,k2_struct_0(sK0)) | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),X0)) ) | (~spl5_10 | ~spl5_17 | ~spl5_23)),
% 0.21/0.52    inference(forward_demodulation,[],[f261,f214])).
% 0.21/0.52  fof(f214,plain,(
% 0.21/0.52    k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0)) | ~spl5_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f212])).
% 0.21/0.52  fof(f261,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k2_struct_0(sK0)) | ~r2_hidden(X1,a_2_1_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),X0)) ) | (~spl5_10 | ~spl5_23)),
% 0.21/0.52    inference(resolution,[],[f250,f131])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl5_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f129])).
% 0.21/0.52  fof(f250,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,X1) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | r2_orders_2(sK0,sK3(X2,sK0,X1),X0)) ) | ~spl5_23),
% 0.21/0.52    inference(avatar_component_clause,[],[f249])).
% 0.21/0.52  fof(f304,plain,(
% 0.21/0.52    spl5_31 | ~spl5_10 | ~spl5_29),
% 0.21/0.52    inference(avatar_split_clause,[],[f299,f285,f129,f301])).
% 0.21/0.52  fof(f285,plain,(
% 0.21/0.52    spl5_29 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | sP4(X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.21/0.52  fof(f299,plain,(
% 0.21/0.52    sP4(k2_struct_0(sK0)) | (~spl5_10 | ~spl5_29)),
% 0.21/0.52    inference(resolution,[],[f286,f131])).
% 0.21/0.52  fof(f286,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | sP4(X0)) ) | ~spl5_29),
% 0.21/0.52    inference(avatar_component_clause,[],[f285])).
% 0.21/0.52  fof(f297,plain,(
% 0.21/0.52    spl5_30 | ~spl5_10 | ~spl5_17 | ~spl5_22 | ~spl5_25 | ~spl5_28),
% 0.21/0.52    inference(avatar_split_clause,[],[f292,f280,f257,f240,f212,f129,f294])).
% 0.21/0.52  fof(f280,plain,(
% 0.21/0.52    spl5_28 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(sK3(X1,sK0,X0),k2_struct_0(sK0)) | ~r2_hidden(X1,a_2_1_orders_2(sK0,X0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.21/0.52  fof(f292,plain,(
% 0.21/0.52    r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | (~spl5_10 | ~spl5_17 | ~spl5_22 | ~spl5_25 | ~spl5_28)),
% 0.21/0.52    inference(subsumption_resolution,[],[f291,f258])).
% 0.21/0.52  fof(f291,plain,(
% 0.21/0.52    ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) | r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | (~spl5_10 | ~spl5_17 | ~spl5_22 | ~spl5_28)),
% 0.21/0.52    inference(forward_demodulation,[],[f290,f214])).
% 0.21/0.52  fof(f290,plain,(
% 0.21/0.52    r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0))) | (~spl5_10 | ~spl5_22 | ~spl5_28)),
% 0.21/0.52    inference(subsumption_resolution,[],[f289,f131])).
% 0.21/0.52  fof(f289,plain,(
% 0.21/0.52    r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0))) | (~spl5_22 | ~spl5_28)),
% 0.21/0.52    inference(superposition,[],[f281,f242])).
% 0.21/0.52  fof(f281,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK3(X1,sK0,X0),k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X1,a_2_1_orders_2(sK0,X0))) ) | ~spl5_28),
% 0.21/0.52    inference(avatar_component_clause,[],[f280])).
% 0.21/0.52  fof(f287,plain,(
% 0.21/0.52    spl5_29 | ~spl5_27),
% 0.21/0.52    inference(avatar_split_clause,[],[f283,f276,f285])).
% 0.21/0.52  fof(f276,plain,(
% 0.21/0.52    spl5_27 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.52  fof(f283,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | sP4(X0)) ) | ~spl5_27),
% 0.21/0.52    inference(resolution,[],[f278,f74])).
% 0.21/0.52  fof(f278,plain,(
% 0.21/0.52    v1_xboole_0(k2_struct_0(sK0)) | ~spl5_27),
% 0.21/0.52    inference(avatar_component_clause,[],[f276])).
% 0.21/0.52  fof(f282,plain,(
% 0.21/0.52    spl5_27 | spl5_28 | ~spl5_19),
% 0.21/0.52    inference(avatar_split_clause,[],[f231,f224,f280,f276])).
% 0.21/0.52  fof(f224,plain,(
% 0.21/0.52    spl5_19 <=> ! [X1,X0] : (m1_subset_1(sK3(X0,sK0,X1),k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.52  fof(f231,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X1,a_2_1_orders_2(sK0,X0)) | v1_xboole_0(k2_struct_0(sK0)) | r2_hidden(sK3(X1,sK0,X0),k2_struct_0(sK0))) ) | ~spl5_19),
% 0.21/0.52    inference(resolution,[],[f225,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.52  fof(f225,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(sK3(X0,sK0,X1),k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1))) ) | ~spl5_19),
% 0.21/0.52    inference(avatar_component_clause,[],[f224])).
% 0.21/0.52  fof(f267,plain,(
% 0.21/0.52    spl5_7 | spl5_25),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f266])).
% 0.21/0.52  fof(f266,plain,(
% 0.21/0.52    $false | (spl5_7 | spl5_25)),
% 0.21/0.52    inference(subsumption_resolution,[],[f264,f111])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) | spl5_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f109])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    spl5_7 <=> k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.52  fof(f264,plain,(
% 0.21/0.52    k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0)) | spl5_25),
% 0.21/0.52    inference(resolution,[],[f259,f60])).
% 0.21/0.52  fof(f259,plain,(
% 0.21/0.52    ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) | spl5_25),
% 0.21/0.52    inference(avatar_component_clause,[],[f257])).
% 0.21/0.52  fof(f260,plain,(
% 0.21/0.52    spl5_24 | ~spl5_25 | ~spl5_10 | ~spl5_17 | ~spl5_19 | ~spl5_22),
% 0.21/0.52    inference(avatar_split_clause,[],[f247,f240,f224,f212,f129,f257,f253])).
% 0.21/0.52  fof(f247,plain,(
% 0.21/0.52    ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) | m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | (~spl5_10 | ~spl5_17 | ~spl5_19 | ~spl5_22)),
% 0.21/0.52    inference(forward_demodulation,[],[f246,f214])).
% 0.21/0.52  fof(f246,plain,(
% 0.21/0.52    m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0))) | (~spl5_10 | ~spl5_19 | ~spl5_22)),
% 0.21/0.52    inference(subsumption_resolution,[],[f245,f131])).
% 0.21/0.52  fof(f245,plain,(
% 0.21/0.52    m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0))) | (~spl5_19 | ~spl5_22)),
% 0.21/0.52    inference(superposition,[],[f225,f242])).
% 0.21/0.52  fof(f251,plain,(
% 0.21/0.52    spl5_23 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f210,f121,f98,f93,f88,f83,f78,f249])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    spl5_1 <=> v2_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    spl5_2 <=> v3_orders_2(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    spl5_3 <=> v4_orders_2(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    spl5_4 <=> v5_orders_2(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.52  fof(f210,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,X1) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | r2_orders_2(sK0,sK3(X2,sK0,X1),X0)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_9)),
% 0.21/0.52    inference(forward_demodulation,[],[f209,f123])).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK3(X2,sK0,X1),X0)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f208,f80])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ~v2_struct_0(sK0) | spl5_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f78])).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK3(X2,sK0,X1),X0) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f207,f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    v3_orders_2(sK0) | ~spl5_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f83])).
% 0.21/0.52  fof(f207,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK3(X2,sK0,X1),X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f206,f90])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    v4_orders_2(sK0) | ~spl5_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f88])).
% 0.21/0.52  fof(f206,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK3(X2,sK0,X1),X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f205,f100])).
% 0.21/0.52  fof(f205,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | r2_orders_2(sK0,sK3(X2,sK0,X1),X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_4),
% 0.21/0.52    inference(resolution,[],[f203,f95])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    v5_orders_2(sK0) | ~spl5_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f93])).
% 0.21/0.52  fof(f203,plain,(
% 0.21/0.52    ( ! [X6,X2,X0,X1] : (~v5_orders_2(X1) | ~r2_hidden(X6,X2) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f64,f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK2(X1,X2,X3)) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f41,f43,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK2(X1,X2,X3)) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.52    inference(rectify,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.52    inference(flattening,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 0.21/0.52  fof(f243,plain,(
% 0.21/0.52    spl5_22 | spl5_7 | ~spl5_20),
% 0.21/0.52    inference(avatar_split_clause,[],[f234,f228,f109,f240])).
% 0.21/0.52  fof(f228,plain,(
% 0.21/0.52    spl5_20 <=> ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | sK3(X0,sK0,k2_struct_0(sK0)) = X0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.52  fof(f234,plain,(
% 0.21/0.52    sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)) | (spl5_7 | ~spl5_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f232,f111])).
% 0.21/0.52  fof(f232,plain,(
% 0.21/0.52    sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)) | k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0)) | ~spl5_20),
% 0.21/0.52    inference(resolution,[],[f229,f60])).
% 0.21/0.52  fof(f229,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | sK3(X0,sK0,k2_struct_0(sK0)) = X0) ) | ~spl5_20),
% 0.21/0.52    inference(avatar_component_clause,[],[f228])).
% 0.21/0.52  fof(f230,plain,(
% 0.21/0.52    spl5_20 | ~spl5_10 | ~spl5_17 | ~spl5_18),
% 0.21/0.52    inference(avatar_split_clause,[],[f222,f218,f212,f129,f228])).
% 0.21/0.52  fof(f218,plain,(
% 0.21/0.52    spl5_18 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | sK3(X0,sK0,X1) = X0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.52  fof(f222,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | sK3(X0,sK0,k2_struct_0(sK0)) = X0) ) | (~spl5_10 | ~spl5_17 | ~spl5_18)),
% 0.21/0.53    inference(forward_demodulation,[],[f221,f214])).
% 0.21/0.53  fof(f221,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0))) | sK3(X0,sK0,k2_struct_0(sK0)) = X0) ) | (~spl5_10 | ~spl5_18)),
% 0.21/0.53    inference(resolution,[],[f219,f131])).
% 0.21/0.53  % (2144)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.53  fof(f219,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | sK3(X0,sK0,X1) = X0) ) | ~spl5_18),
% 0.21/0.53    inference(avatar_component_clause,[],[f218])).
% 0.21/0.53  fof(f226,plain,(
% 0.21/0.53    spl5_19 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f185,f121,f98,f93,f88,f83,f78,f224])).
% 0.21/0.53  fof(f185,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(sK3(X0,sK0,X1),k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_9)),
% 0.21/0.53    inference(forward_demodulation,[],[f184,f123])).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_9)),
% 0.21/0.53    inference(forward_demodulation,[],[f183,f123])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f182,f80])).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f181,f85])).
% 0.21/0.53  fof(f181,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f180,f90])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f179,f100])).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_4),
% 0.21/0.53    inference(resolution,[],[f62,f95])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v5_orders_2(X1) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f220,plain,(
% 0.21/0.53    spl5_18 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f169,f121,f98,f93,f88,f83,f78,f218])).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | sK3(X0,sK0,X1) = X0) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_9)),
% 0.21/0.53    inference(forward_demodulation,[],[f168,f123])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | sK3(X0,sK0,X1) = X0) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f167,f80])).
% 0.21/0.53  fof(f167,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | sK3(X0,sK0,X1) = X0 | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f166,f85])).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | sK3(X0,sK0,X1) = X0 | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f165,f90])).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | sK3(X0,sK0,X1) = X0 | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f164,f100])).
% 0.21/0.53  fof(f164,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | sK3(X0,sK0,X1) = X0 | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_4),
% 0.21/0.53    inference(resolution,[],[f63,f95])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v5_orders_2(X1) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | sK3(X0,X1,X2) = X0 | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f215,plain,(
% 0.21/0.53    spl5_17 | ~spl5_10 | ~spl5_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f204,f200,f129,f212])).
% 0.21/0.53  fof(f200,plain,(
% 0.21/0.53    spl5_16 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.53  fof(f204,plain,(
% 0.21/0.53    k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0)) | (~spl5_10 | ~spl5_16)),
% 0.21/0.53    inference(resolution,[],[f201,f131])).
% 0.21/0.53  fof(f201,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)) ) | ~spl5_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f200])).
% 0.21/0.53  fof(f202,plain,(
% 0.21/0.53    spl5_16 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f161,f121,f98,f93,f88,f83,f78,f200])).
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_9)),
% 0.21/0.53    inference(forward_demodulation,[],[f160,f123])).
% 0.21/0.53  fof(f160,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f159,f80])).
% 0.21/0.53  fof(f159,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f158,f85])).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f157,f90])).
% 0.21/0.53  fof(f157,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f156,f100])).
% 0.21/0.53  fof(f156,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_4),
% 0.21/0.53    inference(resolution,[],[f59,f95])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v5_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    spl5_12 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f146,f121,f116,f98,f93,f88,f83,f78,f148])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    spl5_12 <=> k2_struct_0(sK0) = k2_orders_2(sK0,k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    spl5_8 <=> k1_xboole_0 = k1_struct_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    k2_struct_0(sK0) = k2_orders_2(sK0,k1_xboole_0) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_9)),
% 0.21/0.53    inference(forward_demodulation,[],[f145,f123])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    u1_struct_0(sK0) = k2_orders_2(sK0,k1_xboole_0) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8)),
% 0.21/0.53    inference(forward_demodulation,[],[f144,f118])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    k1_xboole_0 = k1_struct_0(sK0) | ~spl5_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f116])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    u1_struct_0(sK0) = k2_orders_2(sK0,k1_struct_0(sK0)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f143,f80])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    u1_struct_0(sK0) = k2_orders_2(sK0,k1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f142,f85])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    u1_struct_0(sK0) = k2_orders_2(sK0,k1_struct_0(sK0)) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | (~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f141,f90])).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    u1_struct_0(sK0) = k2_orders_2(sK0,k1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f140,f100])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    ~l1_orders_2(sK0) | u1_struct_0(sK0) = k2_orders_2(sK0,k1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl5_4),
% 0.21/0.53    inference(resolution,[],[f58,f95])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0] : (~v5_orders_2(X0) | ~l1_orders_2(X0) | u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_orders_2)).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    spl5_10 | ~spl5_6 | ~spl5_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f127,f121,f104,f129])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    spl5_6 <=> l1_struct_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl5_6 | ~spl5_9)),
% 0.21/0.53    inference(subsumption_resolution,[],[f126,f106])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    l1_struct_0(sK0) | ~spl5_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f104])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_struct_0(sK0) | ~spl5_9),
% 0.21/0.53    inference(superposition,[],[f53,f123])).
% 0.21/0.53  % (2150)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    spl5_9 | ~spl5_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f114,f104,f121])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl5_6),
% 0.21/0.53    inference(resolution,[],[f52,f106])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    spl5_8 | ~spl5_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f113,f104,f116])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    k1_xboole_0 = k1_struct_0(sK0) | ~spl5_6),
% 0.21/0.53    inference(resolution,[],[f51,f106])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_struct_0(X0) | k1_xboole_0 = k1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    ~spl5_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f50,f109])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 0.21/0.53    inference(negated_conjecture,[],[f13])).
% 0.21/0.53  fof(f13,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    spl5_6 | ~spl5_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f102,f98,f104])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    l1_struct_0(sK0) | ~spl5_5),
% 0.21/0.53    inference(resolution,[],[f54,f100])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    spl5_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f49,f98])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    l1_orders_2(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    spl5_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f48,f93])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    v5_orders_2(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    spl5_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f47,f88])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    v4_orders_2(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    spl5_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f46,f83])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    v3_orders_2(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ~spl5_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f45,f78])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ~v2_struct_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (2143)------------------------------
% 0.21/0.53  % (2143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2141)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (2143)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (2143)Memory used [KB]: 6396
% 0.21/0.53  % (2143)Time elapsed: 0.112 s
% 0.21/0.53  % (2143)------------------------------
% 0.21/0.53  % (2143)------------------------------
% 0.21/0.53  % (2140)Success in time 0.167 s
%------------------------------------------------------------------------------
