%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 111 expanded)
%              Number of leaves         :   16 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :  178 ( 306 expanded)
%              Number of equality atoms :    9 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f138,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f68,f72,f81,f93,f104,f116,f134,f137])).

fof(f137,plain,
    ( spl5_1
    | ~ spl5_11
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | spl5_1
    | ~ spl5_11
    | spl5_13 ),
    inference(unit_resulting_resolution,[],[f115,f37,f133,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f133,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl5_13
  <=> r2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f37,plain,
    ( sK0 != sK1
    | spl5_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl5_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f115,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl5_11
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f134,plain,
    ( ~ spl5_13
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f129,f79,f131])).

fof(f79,plain,
    ( spl5_9
  <=> ! [X1] :
        ( r2_hidden(X1,sK1)
        | ~ r2_hidden(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f129,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    | ~ spl5_9 ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    | ~ r2_xboole_0(sK1,sK0)
    | ~ spl5_9 ),
    inference(resolution,[],[f106,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f106,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK1,X0),sK0)
        | ~ r2_xboole_0(sK1,X0) )
    | ~ spl5_9 ),
    inference(resolution,[],[f80,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f80,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f79])).

fof(f116,plain,
    ( spl5_11
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f111,f40,f113])).

fof(f40,plain,
    ( spl5_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f111,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f59,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f59,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(X1,sK0),sK1)
        | r1_tarski(X1,sK0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f44,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f42,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f42,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f104,plain,
    ( spl5_4
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | spl5_4
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f67,f55,f18])).

fof(f18,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f55,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_4
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f67,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl5_6
  <=> ! [X0] : ~ r2_hidden(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f93,plain,
    ( ~ spl5_4
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f92,f70,f54])).

fof(f70,plain,
    ( spl5_7
  <=> ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f92,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_7 ),
    inference(condensation,[],[f89])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(sK1) )
    | ~ spl5_7 ),
    inference(resolution,[],[f71,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f71,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ v1_xboole_0(X0) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f81,plain,
    ( spl5_5
    | spl5_9 ),
    inference(avatar_split_clause,[],[f48,f79,f62])).

fof(f62,plain,
    ( spl5_5
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f48,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f15,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f15,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => r2_hidden(X2,X1) )
         => X0 = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

fof(f72,plain,
    ( ~ spl5_5
    | spl5_7 ),
    inference(avatar_split_clause,[],[f47,f70,f62])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ v1_xboole_0(X0)
      | ~ v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f15,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f68,plain,
    ( ~ spl5_5
    | spl5_6
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f58,f40,f66,f62])).

fof(f58,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ v1_xboole_0(sK0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f44,f19])).

fof(f43,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f16,f40])).

fof(f16,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f38,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f17,f35])).

fof(f17,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:05:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (32429)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (32440)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (32432)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (32439)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (32429)Refutation not found, incomplete strategy% (32429)------------------------------
% 0.21/0.51  % (32429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32429)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (32429)Memory used [KB]: 10618
% 0.21/0.51  % (32429)Time elapsed: 0.090 s
% 0.21/0.51  % (32429)------------------------------
% 0.21/0.51  % (32429)------------------------------
% 0.21/0.52  % (32439)Refutation not found, incomplete strategy% (32439)------------------------------
% 0.21/0.52  % (32439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (32439)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (32439)Memory used [KB]: 1663
% 0.21/0.52  % (32439)Time elapsed: 0.106 s
% 0.21/0.52  % (32439)------------------------------
% 0.21/0.52  % (32439)------------------------------
% 0.21/0.52  % (32438)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (32440)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f38,f43,f68,f72,f81,f93,f104,f116,f134,f137])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    spl5_1 | ~spl5_11 | spl5_13),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f135])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    $false | (spl5_1 | ~spl5_11 | spl5_13)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f115,f37,f133,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    ~r2_xboole_0(sK1,sK0) | spl5_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f131])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    spl5_13 <=> r2_xboole_0(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    sK0 != sK1 | spl5_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    spl5_1 <=> sK0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    r1_tarski(sK1,sK0) | ~spl5_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f113])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    spl5_11 <=> r1_tarski(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    ~spl5_13 | ~spl5_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f129,f79,f131])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    spl5_9 <=> ! [X1] : (r2_hidden(X1,sK1) | ~r2_hidden(X1,sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    ~r2_xboole_0(sK1,sK0) | ~spl5_9),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f128])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    ~r2_xboole_0(sK1,sK0) | ~r2_xboole_0(sK1,sK0) | ~spl5_9),
% 0.21/0.52    inference(resolution,[],[f106,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(sK4(sK1,X0),sK0) | ~r2_xboole_0(sK1,X0)) ) | ~spl5_9),
% 0.21/0.52    inference(resolution,[],[f80,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ( ! [X1] : (r2_hidden(X1,sK1) | ~r2_hidden(X1,sK0)) ) | ~spl5_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f79])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    spl5_11 | ~spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f111,f40,f113])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    spl5_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    r1_tarski(sK1,sK0) | ~spl5_2),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f110])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0) | ~spl5_2),
% 0.21/0.52    inference(resolution,[],[f59,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X1] : (~r2_hidden(sK3(X1,sK0),sK1) | r1_tarski(X1,sK0)) ) | ~spl5_2),
% 0.21/0.52    inference(resolution,[],[f44,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1)) ) | ~spl5_2),
% 0.21/0.52    inference(resolution,[],[f42,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl5_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f40])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    spl5_4 | ~spl5_6),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f103])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    $false | (spl5_4 | ~spl5_6)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f67,f55,f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ~v1_xboole_0(sK1) | spl5_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    spl5_4 <=> v1_xboole_0(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | ~spl5_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    spl5_6 <=> ! [X0] : ~r2_hidden(X0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ~spl5_4 | ~spl5_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f92,f70,f54])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    spl5_7 <=> ! [X0] : (r2_hidden(X0,sK1) | ~v1_xboole_0(X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    ~v1_xboole_0(sK1) | ~spl5_7),
% 0.21/0.52    inference(condensation,[],[f89])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(X0) | ~v1_xboole_0(sK1)) ) | ~spl5_7),
% 0.21/0.52    inference(resolution,[],[f71,f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(X0,sK1) | ~v1_xboole_0(X0)) ) | ~spl5_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f70])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    spl5_5 | spl5_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f48,f79,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    spl5_5 <=> v1_xboole_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X1] : (r2_hidden(X1,sK1) | ~r2_hidden(X1,sK0) | v1_xboole_0(sK0)) )),
% 0.21/0.52    inference(resolution,[],[f15,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ( ! [X2] : (~m1_subset_1(X2,sK0) | r2_hidden(X2,sK1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ? [X0,X1] : (X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(flattening,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0,X1] : ((X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.21/0.52    inference(negated_conjecture,[],[f7])).
% 0.21/0.52  fof(f7,conjecture,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ~spl5_5 | spl5_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f47,f70,f62])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(X0,sK1) | ~v1_xboole_0(X0) | ~v1_xboole_0(sK0)) )),
% 0.21/0.52    inference(resolution,[],[f15,f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ~spl5_5 | spl5_6 | ~spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f58,f40,f66,f62])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(sK0)) ) | ~spl5_2),
% 0.21/0.52    inference(resolution,[],[f44,f19])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f16,f40])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ~spl5_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f17,f35])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    sK0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (32440)------------------------------
% 0.21/0.52  % (32440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (32440)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (32440)Memory used [KB]: 10746
% 0.21/0.52  % (32440)Time elapsed: 0.059 s
% 0.21/0.52  % (32440)------------------------------
% 0.21/0.52  % (32440)------------------------------
% 0.21/0.52  % (32412)Success in time 0.159 s
%------------------------------------------------------------------------------
