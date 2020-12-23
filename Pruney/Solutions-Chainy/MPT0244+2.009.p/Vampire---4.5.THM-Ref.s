%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 194 expanded)
%              Number of leaves         :   15 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  197 ( 460 expanded)
%              Number of equality atoms :   48 ( 123 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f178,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f66,f67,f72,f114,f129,f134,f177])).

fof(f177,plain,
    ( spl4_4
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl4_4
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f135,f128,f167])).

fof(f167,plain,(
    ! [X8,X7] :
      ( r1_xboole_0(X8,k2_enumset1(X7,X7,X7,X7))
      | r2_hidden(X7,X8) ) ),
    inference(resolution,[],[f149,f101])).

fof(f101,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f82,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f82,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(sK2(X2,X3),X4)
      | ~ r1_xboole_0(X4,X2)
      | r1_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f20,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f149,plain,(
    ! [X6,X7] :
      ( r1_xboole_0(k2_enumset1(X6,X6,X6,X6),X7)
      | r2_hidden(X6,X7) ) ),
    inference(duplicate_literal_removal,[],[f146])).

fof(f146,plain,(
    ! [X6,X7] :
      ( r2_hidden(X6,X7)
      | r1_xboole_0(k2_enumset1(X6,X6,X6,X6),X7)
      | r1_xboole_0(k2_enumset1(X6,X6,X6,X6),X7) ) ),
    inference(superposition,[],[f22,f96])).

fof(f96,plain,(
    ! [X2,X1] :
      ( sK2(k2_enumset1(X1,X1,X1,X1),X2) = X1
      | r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) ) ),
    inference(resolution,[],[f50,f21])).

fof(f50,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f29,f38])).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f18,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f19,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f18,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f128,plain,
    ( ~ r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl4_4
  <=> r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f135,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl4_5 ),
    inference(resolution,[],[f133,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f38])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f133,plain,
    ( ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl4_5
  <=> r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f134,plain,
    ( spl4_2
    | ~ spl4_5
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f124,f54,f131,f58])).

fof(f58,plain,
    ( spl4_2
  <=> sK0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f54,plain,
    ( spl4_1
  <=> r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f124,plain,
    ( ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f56,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f56,plain,
    ( r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f129,plain,
    ( ~ spl4_4
    | spl4_3
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f123,f54,f62,f126])).

fof(f62,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f123,plain,
    ( k1_xboole_0 = sK0
    | ~ r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl4_1 ),
    inference(resolution,[],[f56,f76])).

fof(f76,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | k1_xboole_0 = X2
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f34,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f114,plain,
    ( spl4_1
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f73,f105])).

fof(f105,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f89,f104])).

fof(f104,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f102,f87])).

fof(f87,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f86,f48])).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f86,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != X2
      | r1_xboole_0(X2,X3)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f26,f34])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f82,f21])).

fof(f89,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k1_xboole_0,X0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != X2
      | r1_tarski(X2,X3)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f35,f27])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f73,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl4_1
    | ~ spl4_3 ),
    inference(superposition,[],[f55,f64])).

fof(f64,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f55,plain,
    ( ~ r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f72,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | spl4_1
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f48,f68])).

fof(f68,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl4_1
    | ~ spl4_2 ),
    inference(superposition,[],[f55,f60])).

fof(f60,plain,
    ( sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f67,plain,
    ( ~ spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f41,f62,f54])).

fof(f41,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f15,f38])).

fof(f15,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <~> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,k1_tarski(X1))
      <=> ( k1_tarski(X1) = X0
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f66,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f40,f58,f54])).

fof(f40,plain,
    ( sK0 != k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f16,f38,f38])).

fof(f16,plain,
    ( sK0 != k1_tarski(sK1)
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f65,plain,
    ( spl4_1
    | spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f39,f62,f58,f54])).

fof(f39,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f17,f38,f38])).

fof(f17,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1)
    | r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:16:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.53  % (14341)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.54  % (14350)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.55  % (14363)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.55  % (14350)Refutation not found, incomplete strategy% (14350)------------------------------
% 0.20/0.55  % (14350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (14350)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (14350)Memory used [KB]: 6140
% 0.20/0.55  % (14350)Time elapsed: 0.129 s
% 0.20/0.55  % (14350)------------------------------
% 0.20/0.55  % (14350)------------------------------
% 0.20/0.55  % (14340)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.55  % (14340)Refutation not found, incomplete strategy% (14340)------------------------------
% 0.20/0.55  % (14340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (14340)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (14340)Memory used [KB]: 1663
% 0.20/0.55  % (14340)Time elapsed: 0.097 s
% 0.20/0.55  % (14340)------------------------------
% 0.20/0.55  % (14340)------------------------------
% 0.20/0.55  % (14342)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.56  % (14347)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.56  % (14345)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  % (14363)Refutation not found, incomplete strategy% (14363)------------------------------
% 0.20/0.56  % (14363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (14363)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (14363)Memory used [KB]: 10618
% 0.20/0.56  % (14363)Time elapsed: 0.142 s
% 0.20/0.56  % (14363)------------------------------
% 0.20/0.56  % (14363)------------------------------
% 0.20/0.57  % (14352)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.57  % (14362)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.57  % (14354)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.57  % (14358)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.58  % (14344)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.58  % (14346)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.58  % (14343)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.59  % (14368)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.59  % (14352)Refutation found. Thanks to Tanya!
% 0.20/0.59  % SZS status Theorem for theBenchmark
% 0.20/0.59  % SZS output start Proof for theBenchmark
% 0.20/0.59  fof(f178,plain,(
% 0.20/0.59    $false),
% 0.20/0.59    inference(avatar_sat_refutation,[],[f65,f66,f67,f72,f114,f129,f134,f177])).
% 0.20/0.59  fof(f177,plain,(
% 0.20/0.59    spl4_4 | spl4_5),
% 0.20/0.59    inference(avatar_contradiction_clause,[],[f169])).
% 0.20/0.59  fof(f169,plain,(
% 0.20/0.59    $false | (spl4_4 | spl4_5)),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f135,f128,f167])).
% 0.20/0.59  fof(f167,plain,(
% 0.20/0.59    ( ! [X8,X7] : (r1_xboole_0(X8,k2_enumset1(X7,X7,X7,X7)) | r2_hidden(X7,X8)) )),
% 0.20/0.59    inference(resolution,[],[f149,f101])).
% 0.20/0.59  fof(f101,plain,(
% 0.20/0.59    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2)) )),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f99])).
% 0.20/0.59  fof(f99,plain,(
% 0.20/0.59    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) )),
% 0.20/0.59    inference(resolution,[],[f82,f22])).
% 0.20/0.59  fof(f22,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f14])).
% 0.20/0.59  fof(f14,plain,(
% 0.20/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.59    inference(ennf_transformation,[],[f12])).
% 0.20/0.59  fof(f12,plain,(
% 0.20/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.59    inference(rectify,[],[f1])).
% 0.20/0.59  fof(f1,axiom,(
% 0.20/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.59  fof(f82,plain,(
% 0.20/0.59    ( ! [X4,X2,X3] : (~r2_hidden(sK2(X2,X3),X4) | ~r1_xboole_0(X4,X2) | r1_xboole_0(X2,X3)) )),
% 0.20/0.59    inference(resolution,[],[f20,f21])).
% 0.20/0.59  fof(f21,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f14])).
% 0.20/0.59  fof(f20,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f14])).
% 0.20/0.59  fof(f149,plain,(
% 0.20/0.59    ( ! [X6,X7] : (r1_xboole_0(k2_enumset1(X6,X6,X6,X6),X7) | r2_hidden(X6,X7)) )),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f146])).
% 0.20/0.59  fof(f146,plain,(
% 0.20/0.59    ( ! [X6,X7] : (r2_hidden(X6,X7) | r1_xboole_0(k2_enumset1(X6,X6,X6,X6),X7) | r1_xboole_0(k2_enumset1(X6,X6,X6,X6),X7)) )),
% 0.20/0.59    inference(superposition,[],[f22,f96])).
% 0.20/0.59  fof(f96,plain,(
% 0.20/0.59    ( ! [X2,X1] : (sK2(k2_enumset1(X1,X1,X1,X1),X2) = X1 | r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)) )),
% 0.20/0.59    inference(resolution,[],[f50,f21])).
% 0.20/0.59  fof(f50,plain,(
% 0.20/0.59    ( ! [X2,X0] : (~r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) | X0 = X2) )),
% 0.20/0.59    inference(equality_resolution,[],[f44])).
% 0.20/0.59  fof(f44,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.20/0.59    inference(definition_unfolding,[],[f29,f38])).
% 0.20/0.59  fof(f38,plain,(
% 0.20/0.59    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.59    inference(definition_unfolding,[],[f18,f37])).
% 0.20/0.59  fof(f37,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.59    inference(definition_unfolding,[],[f19,f36])).
% 0.20/0.59  fof(f36,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f8])).
% 0.20/0.59  fof(f8,axiom,(
% 0.20/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.59  fof(f19,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f7])).
% 0.20/0.59  fof(f7,axiom,(
% 0.20/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.59  fof(f18,plain,(
% 0.20/0.59    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f6])).
% 0.20/0.59  fof(f6,axiom,(
% 0.20/0.59    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.59  fof(f29,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.59    inference(cnf_transformation,[],[f5])).
% 0.20/0.59  fof(f5,axiom,(
% 0.20/0.59    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.59  fof(f128,plain,(
% 0.20/0.59    ~r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | spl4_4),
% 0.20/0.59    inference(avatar_component_clause,[],[f126])).
% 0.20/0.59  fof(f126,plain,(
% 0.20/0.59    spl4_4 <=> r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.59  fof(f135,plain,(
% 0.20/0.59    ~r2_hidden(sK1,sK0) | spl4_5),
% 0.20/0.59    inference(resolution,[],[f133,f47])).
% 0.20/0.59  fof(f47,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.59    inference(definition_unfolding,[],[f32,f38])).
% 0.20/0.59  fof(f32,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f9])).
% 0.20/0.59  fof(f9,axiom,(
% 0.20/0.59    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.59  fof(f133,plain,(
% 0.20/0.59    ~r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | spl4_5),
% 0.20/0.59    inference(avatar_component_clause,[],[f131])).
% 0.20/0.59  fof(f131,plain,(
% 0.20/0.59    spl4_5 <=> r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.59  fof(f134,plain,(
% 0.20/0.59    spl4_2 | ~spl4_5 | ~spl4_1),
% 0.20/0.59    inference(avatar_split_clause,[],[f124,f54,f131,f58])).
% 0.20/0.59  fof(f58,plain,(
% 0.20/0.59    spl4_2 <=> sK0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.59  fof(f54,plain,(
% 0.20/0.59    spl4_1 <=> r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.59  fof(f124,plain,(
% 0.20/0.59    ~r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl4_1),
% 0.20/0.59    inference(resolution,[],[f56,f25])).
% 0.20/0.59  fof(f25,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.59    inference(cnf_transformation,[],[f2])).
% 0.20/0.59  fof(f2,axiom,(
% 0.20/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.59  fof(f56,plain,(
% 0.20/0.59    r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl4_1),
% 0.20/0.59    inference(avatar_component_clause,[],[f54])).
% 0.20/0.59  fof(f129,plain,(
% 0.20/0.59    ~spl4_4 | spl4_3 | ~spl4_1),
% 0.20/0.59    inference(avatar_split_clause,[],[f123,f54,f62,f126])).
% 0.20/0.59  fof(f62,plain,(
% 0.20/0.59    spl4_3 <=> k1_xboole_0 = sK0),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.59  fof(f123,plain,(
% 0.20/0.59    k1_xboole_0 = sK0 | ~r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl4_1),
% 0.20/0.59    inference(resolution,[],[f56,f76])).
% 0.20/0.59  fof(f76,plain,(
% 0.20/0.59    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k1_xboole_0 = X2 | ~r1_xboole_0(X2,X3)) )),
% 0.20/0.59    inference(superposition,[],[f34,f27])).
% 0.20/0.59  fof(f27,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f4])).
% 0.20/0.59  fof(f4,axiom,(
% 0.20/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.59  fof(f34,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f3])).
% 0.20/0.59  fof(f3,axiom,(
% 0.20/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.59  fof(f114,plain,(
% 0.20/0.59    spl4_1 | ~spl4_3),
% 0.20/0.59    inference(avatar_contradiction_clause,[],[f110])).
% 0.20/0.59  fof(f110,plain,(
% 0.20/0.59    $false | (spl4_1 | ~spl4_3)),
% 0.20/0.59    inference(subsumption_resolution,[],[f73,f105])).
% 0.20/0.59  fof(f105,plain,(
% 0.20/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.59    inference(subsumption_resolution,[],[f89,f104])).
% 0.20/0.59  fof(f104,plain,(
% 0.20/0.59    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.59    inference(resolution,[],[f102,f87])).
% 0.20/0.59  fof(f87,plain,(
% 0.20/0.59    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.59    inference(resolution,[],[f86,f48])).
% 0.20/0.59  fof(f48,plain,(
% 0.20/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.59    inference(equality_resolution,[],[f24])).
% 0.20/0.59  fof(f24,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.59    inference(cnf_transformation,[],[f2])).
% 0.20/0.59  fof(f86,plain,(
% 0.20/0.59    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | r1_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.59    inference(equality_resolution,[],[f78])).
% 0.20/0.59  fof(f78,plain,(
% 0.20/0.59    ( ! [X2,X3] : (k1_xboole_0 != X2 | r1_xboole_0(X2,X3) | ~r1_tarski(X2,X3)) )),
% 0.20/0.59    inference(superposition,[],[f26,f34])).
% 0.20/0.59  fof(f26,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f4])).
% 0.20/0.59  fof(f102,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1)) )),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f98])).
% 0.20/0.59  fof(f98,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.59    inference(resolution,[],[f82,f21])).
% 0.20/0.59  fof(f89,plain,(
% 0.20/0.59    ( ! [X0] : (~r1_xboole_0(k1_xboole_0,X0) | r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.59    inference(equality_resolution,[],[f80])).
% 0.20/0.59  fof(f80,plain,(
% 0.20/0.59    ( ! [X2,X3] : (k1_xboole_0 != X2 | r1_tarski(X2,X3) | ~r1_xboole_0(X2,X3)) )),
% 0.20/0.59    inference(superposition,[],[f35,f27])).
% 0.20/0.59  fof(f35,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f3])).
% 0.20/0.59  fof(f73,plain,(
% 0.20/0.59    ~r1_tarski(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1)) | (spl4_1 | ~spl4_3)),
% 0.20/0.59    inference(superposition,[],[f55,f64])).
% 0.20/0.59  fof(f64,plain,(
% 0.20/0.59    k1_xboole_0 = sK0 | ~spl4_3),
% 0.20/0.59    inference(avatar_component_clause,[],[f62])).
% 0.20/0.59  fof(f55,plain,(
% 0.20/0.59    ~r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | spl4_1),
% 0.20/0.59    inference(avatar_component_clause,[],[f54])).
% 0.20/0.59  fof(f72,plain,(
% 0.20/0.59    spl4_1 | ~spl4_2),
% 0.20/0.59    inference(avatar_contradiction_clause,[],[f69])).
% 0.20/0.59  fof(f69,plain,(
% 0.20/0.59    $false | (spl4_1 | ~spl4_2)),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f48,f68])).
% 0.20/0.59  fof(f68,plain,(
% 0.20/0.59    ~r1_tarski(sK0,sK0) | (spl4_1 | ~spl4_2)),
% 0.20/0.59    inference(superposition,[],[f55,f60])).
% 0.20/0.59  fof(f60,plain,(
% 0.20/0.59    sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl4_2),
% 0.20/0.59    inference(avatar_component_clause,[],[f58])).
% 0.20/0.59  fof(f67,plain,(
% 0.20/0.59    ~spl4_1 | ~spl4_3),
% 0.20/0.59    inference(avatar_split_clause,[],[f41,f62,f54])).
% 0.20/0.59  fof(f41,plain,(
% 0.20/0.59    k1_xboole_0 != sK0 | ~r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.20/0.59    inference(definition_unfolding,[],[f15,f38])).
% 0.20/0.59  fof(f15,plain,(
% 0.20/0.59    k1_xboole_0 != sK0 | ~r1_tarski(sK0,k1_tarski(sK1))),
% 0.20/0.59    inference(cnf_transformation,[],[f13])).
% 0.20/0.59  fof(f13,plain,(
% 0.20/0.59    ? [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <~> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.59    inference(ennf_transformation,[],[f11])).
% 0.20/0.59  fof(f11,negated_conjecture,(
% 0.20/0.59    ~! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.59    inference(negated_conjecture,[],[f10])).
% 0.20/0.59  fof(f10,conjecture,(
% 0.20/0.59    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).
% 0.20/0.59  fof(f66,plain,(
% 0.20/0.59    ~spl4_1 | ~spl4_2),
% 0.20/0.59    inference(avatar_split_clause,[],[f40,f58,f54])).
% 0.20/0.59  fof(f40,plain,(
% 0.20/0.59    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) | ~r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.20/0.59    inference(definition_unfolding,[],[f16,f38,f38])).
% 0.20/0.59  fof(f16,plain,(
% 0.20/0.59    sK0 != k1_tarski(sK1) | ~r1_tarski(sK0,k1_tarski(sK1))),
% 0.20/0.59    inference(cnf_transformation,[],[f13])).
% 0.20/0.59  fof(f65,plain,(
% 0.20/0.59    spl4_1 | spl4_2 | spl4_3),
% 0.20/0.59    inference(avatar_split_clause,[],[f39,f62,f58,f54])).
% 0.20/0.59  fof(f39,plain,(
% 0.20/0.59    k1_xboole_0 = sK0 | sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.20/0.59    inference(definition_unfolding,[],[f17,f38,f38])).
% 0.20/0.59  fof(f17,plain,(
% 0.20/0.59    k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1) | r1_tarski(sK0,k1_tarski(sK1))),
% 0.20/0.59    inference(cnf_transformation,[],[f13])).
% 0.20/0.59  % SZS output end Proof for theBenchmark
% 0.20/0.59  % (14352)------------------------------
% 0.20/0.59  % (14352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (14352)Termination reason: Refutation
% 0.20/0.59  
% 0.20/0.59  % (14352)Memory used [KB]: 6268
% 0.20/0.59  % (14352)Time elapsed: 0.174 s
% 0.20/0.59  % (14352)------------------------------
% 0.20/0.59  % (14352)------------------------------
% 0.20/0.59  % (14338)Success in time 0.232 s
%------------------------------------------------------------------------------
