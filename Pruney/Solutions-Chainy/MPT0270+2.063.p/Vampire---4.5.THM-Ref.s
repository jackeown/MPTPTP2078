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
% DateTime   : Thu Dec  3 12:41:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 158 expanded)
%              Number of leaves         :   13 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  166 ( 283 expanded)
%              Number of equality atoms :   61 ( 146 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f216,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f77,f114,f126,f175,f186,f215])).

fof(f215,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f62,f53,f202])).

fof(f202,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X4,sK1) )
    | ~ spl4_1 ),
    inference(superposition,[],[f48,f57])).

fof(f57,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl4_1
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f21,f15])).

fof(f15,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f53,plain,(
    ! [X3,X1] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X1)) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k3_enumset1(X3,X3,X3,X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k3_enumset1(X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f27,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f14,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f16,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f16,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f14,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f62,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl4_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f186,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f51,f174])).

fof(f174,plain,
    ( ~ r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl4_5
  <=> r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f51,plain,(
    ! [X0,X3] : r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X3)) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k3_enumset1(X0,X0,X0,X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k3_enumset1(X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f28,f31])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f175,plain,
    ( spl4_2
    | ~ spl4_5
    | spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f163,f123,f56,f172,f60])).

fof(f123,plain,
    ( spl4_4
  <=> sK0 = sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f163,plain,
    ( ~ r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | r2_hidden(sK0,sK1)
    | spl4_1
    | ~ spl4_4 ),
    inference(trivial_inequality_removal,[],[f162])).

fof(f162,plain,
    ( ~ r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | r2_hidden(sK0,sK1)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | spl4_1
    | ~ spl4_4 ),
    inference(duplicate_literal_removal,[],[f157])).

fof(f157,plain,
    ( ~ r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | spl4_1
    | ~ spl4_4 ),
    inference(superposition,[],[f67,f125])).

fof(f125,plain,
    ( sK0 = sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f123])).

fof(f67,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,X0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
        | r2_hidden(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,X0),sK1)
        | ~ r2_hidden(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,X0),X0)
        | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != X0 )
    | spl4_1 ),
    inference(superposition,[],[f58,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f17,f15])).

% (15734)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f58,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f126,plain,
    ( spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f120,f111,f123])).

fof(f111,plain,
    ( spl4_3
  <=> r2_hidden(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f120,plain,
    ( sK0 = sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl4_3 ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,
    ( sK0 = sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | sK0 = sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f113,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k3_enumset1(X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f26,f31])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f113,plain,
    ( r2_hidden(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f111])).

fof(f114,plain,
    ( spl4_3
    | spl4_1 ),
    inference(avatar_split_clause,[],[f108,f56,f111])).

fof(f108,plain,
    ( r2_hidden(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f103])).

fof(f103,plain,
    ( r2_hidden(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | spl4_1 ),
    inference(factoring,[],[f68])).

fof(f68,plain,
    ( ! [X1] :
        ( r2_hidden(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,X1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
        | r2_hidden(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,X1),X1)
        | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != X1 )
    | spl4_1 ),
    inference(superposition,[],[f58,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f18,f15])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f77,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f34,f60,f56])).

fof(f34,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f11,f32,f15,f32])).

fof(f32,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f13,f31])).

fof(f13,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f11,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f63,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f33,f60,f56])).

fof(f33,plain,
    ( r2_hidden(sK0,sK1)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f12,f32,f15,f32])).

fof(f12,plain,
    ( r2_hidden(sK0,sK1)
    | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:16:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.49  % (15723)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (15718)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.50  % (15729)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.51  % (15746)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.51  % (15729)Refutation not found, incomplete strategy% (15729)------------------------------
% 0.22/0.51  % (15729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15719)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (15738)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.52  % (15746)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (15729)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (15729)Memory used [KB]: 6140
% 0.22/0.52  % (15729)Time elapsed: 0.107 s
% 0.22/0.52  % (15729)------------------------------
% 0.22/0.52  % (15729)------------------------------
% 0.22/0.52  % (15730)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (15722)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (15728)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (15721)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (15726)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.28/0.52  % (15744)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.28/0.52  % (15727)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.28/0.52  % (15732)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.28/0.53  % (15732)Refutation not found, incomplete strategy% (15732)------------------------------
% 1.28/0.53  % (15732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (15732)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (15732)Memory used [KB]: 1663
% 1.28/0.53  % (15732)Time elapsed: 0.084 s
% 1.28/0.53  % (15732)------------------------------
% 1.28/0.53  % (15732)------------------------------
% 1.28/0.53  % SZS output start Proof for theBenchmark
% 1.28/0.53  fof(f216,plain,(
% 1.28/0.53    $false),
% 1.28/0.53    inference(avatar_sat_refutation,[],[f63,f77,f114,f126,f175,f186,f215])).
% 1.28/0.53  fof(f215,plain,(
% 1.28/0.53    ~spl4_1 | ~spl4_2),
% 1.28/0.53    inference(avatar_contradiction_clause,[],[f206])).
% 1.28/0.53  fof(f206,plain,(
% 1.28/0.53    $false | (~spl4_1 | ~spl4_2)),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f62,f53,f202])).
% 1.28/0.53  fof(f202,plain,(
% 1.28/0.53    ( ! [X4] : (~r2_hidden(X4,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X4,sK1)) ) | ~spl4_1),
% 1.28/0.53    inference(superposition,[],[f48,f57])).
% 1.28/0.53  fof(f57,plain,(
% 1.28/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) | ~spl4_1),
% 1.28/0.53    inference(avatar_component_clause,[],[f56])).
% 1.28/0.53  fof(f56,plain,(
% 1.28/0.53    spl4_1 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.28/0.53  fof(f48,plain,(
% 1.28/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X3,X1)) )),
% 1.28/0.53    inference(equality_resolution,[],[f36])).
% 1.28/0.53  fof(f36,plain,(
% 1.28/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.28/0.53    inference(definition_unfolding,[],[f21,f15])).
% 1.28/0.53  fof(f15,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.28/0.53    inference(cnf_transformation,[],[f2])).
% 1.28/0.53  fof(f2,axiom,(
% 1.28/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.28/0.53  fof(f21,plain,(
% 1.28/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.28/0.53    inference(cnf_transformation,[],[f1])).
% 1.28/0.53  fof(f1,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.28/0.53  fof(f53,plain,(
% 1.28/0.53    ( ! [X3,X1] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X1))) )),
% 1.28/0.53    inference(equality_resolution,[],[f52])).
% 1.28/0.53  fof(f52,plain,(
% 1.28/0.53    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k3_enumset1(X3,X3,X3,X3,X1) != X2) )),
% 1.28/0.53    inference(equality_resolution,[],[f42])).
% 1.28/0.53  fof(f42,plain,(
% 1.28/0.53    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k3_enumset1(X0,X0,X0,X0,X1) != X2) )),
% 1.28/0.53    inference(definition_unfolding,[],[f27,f31])).
% 1.28/0.53  fof(f31,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.28/0.53    inference(definition_unfolding,[],[f14,f30])).
% 1.28/0.53  fof(f30,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.28/0.53    inference(definition_unfolding,[],[f16,f29])).
% 1.28/0.53  fof(f29,plain,(
% 1.28/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f7])).
% 1.28/0.53  fof(f7,axiom,(
% 1.28/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.28/0.53  fof(f16,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f6])).
% 1.28/0.53  fof(f6,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.28/0.53  fof(f14,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f5])).
% 1.28/0.53  fof(f5,axiom,(
% 1.28/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.28/0.53  fof(f27,plain,(
% 1.28/0.53    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.28/0.53    inference(cnf_transformation,[],[f3])).
% 1.28/0.53  fof(f3,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.28/0.53  fof(f62,plain,(
% 1.28/0.53    r2_hidden(sK0,sK1) | ~spl4_2),
% 1.28/0.53    inference(avatar_component_clause,[],[f60])).
% 1.28/0.53  fof(f60,plain,(
% 1.28/0.53    spl4_2 <=> r2_hidden(sK0,sK1)),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.28/0.53  fof(f186,plain,(
% 1.28/0.53    spl4_5),
% 1.28/0.53    inference(avatar_contradiction_clause,[],[f177])).
% 1.28/0.53  fof(f177,plain,(
% 1.28/0.53    $false | spl4_5),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f51,f174])).
% 1.28/0.53  fof(f174,plain,(
% 1.28/0.53    ~r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl4_5),
% 1.28/0.53    inference(avatar_component_clause,[],[f172])).
% 1.28/0.53  fof(f172,plain,(
% 1.28/0.53    spl4_5 <=> r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.28/0.53  fof(f51,plain,(
% 1.28/0.53    ( ! [X0,X3] : (r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X3))) )),
% 1.28/0.53    inference(equality_resolution,[],[f50])).
% 1.28/0.53  fof(f50,plain,(
% 1.28/0.53    ( ! [X2,X0,X3] : (r2_hidden(X3,X2) | k3_enumset1(X0,X0,X0,X0,X3) != X2) )),
% 1.28/0.53    inference(equality_resolution,[],[f41])).
% 1.28/0.53  fof(f41,plain,(
% 1.28/0.53    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k3_enumset1(X0,X0,X0,X0,X1) != X2) )),
% 1.28/0.53    inference(definition_unfolding,[],[f28,f31])).
% 1.28/0.53  fof(f28,plain,(
% 1.28/0.53    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.28/0.53    inference(cnf_transformation,[],[f3])).
% 1.28/0.53  fof(f175,plain,(
% 1.28/0.53    spl4_2 | ~spl4_5 | spl4_1 | ~spl4_4),
% 1.28/0.53    inference(avatar_split_clause,[],[f163,f123,f56,f172,f60])).
% 1.28/0.53  fof(f123,plain,(
% 1.28/0.53    spl4_4 <=> sK0 = sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.28/0.53  fof(f163,plain,(
% 1.28/0.53    ~r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(sK0,sK1) | (spl4_1 | ~spl4_4)),
% 1.28/0.53    inference(trivial_inequality_removal,[],[f162])).
% 1.28/0.53  fof(f162,plain,(
% 1.28/0.53    ~r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(sK0,sK1) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | (spl4_1 | ~spl4_4)),
% 1.28/0.53    inference(duplicate_literal_removal,[],[f157])).
% 1.28/0.53  fof(f157,plain,(
% 1.28/0.53    ~r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | (spl4_1 | ~spl4_4)),
% 1.28/0.53    inference(superposition,[],[f67,f125])).
% 1.28/0.53  fof(f125,plain,(
% 1.28/0.53    sK0 = sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl4_4),
% 1.28/0.53    inference(avatar_component_clause,[],[f123])).
% 1.28/0.53  fof(f67,plain,(
% 1.28/0.53    ( ! [X0] : (~r2_hidden(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,X0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,X0),sK1) | ~r2_hidden(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,X0),X0) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != X0) ) | spl4_1),
% 1.28/0.53    inference(superposition,[],[f58,f40])).
% 1.28/0.53  fof(f40,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(sK2(X0,X1,X2),X0)) )),
% 1.28/0.53    inference(definition_unfolding,[],[f17,f15])).
% 1.28/0.53  % (15734)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.28/0.53  fof(f17,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.28/0.53    inference(cnf_transformation,[],[f1])).
% 1.28/0.53  fof(f58,plain,(
% 1.28/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) | spl4_1),
% 1.28/0.53    inference(avatar_component_clause,[],[f56])).
% 1.28/0.53  fof(f126,plain,(
% 1.28/0.53    spl4_4 | ~spl4_3),
% 1.28/0.53    inference(avatar_split_clause,[],[f120,f111,f123])).
% 1.28/0.53  fof(f111,plain,(
% 1.28/0.53    spl4_3 <=> r2_hidden(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.28/0.53  fof(f120,plain,(
% 1.28/0.53    sK0 = sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl4_3),
% 1.28/0.53    inference(duplicate_literal_removal,[],[f115])).
% 1.28/0.53  fof(f115,plain,(
% 1.28/0.53    sK0 = sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | sK0 = sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl4_3),
% 1.28/0.53    inference(resolution,[],[f113,f54])).
% 1.28/0.53  fof(f54,plain,(
% 1.28/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 1.28/0.53    inference(equality_resolution,[],[f43])).
% 1.28/0.53  fof(f43,plain,(
% 1.28/0.53    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k3_enumset1(X0,X0,X0,X0,X1) != X2) )),
% 1.28/0.53    inference(definition_unfolding,[],[f26,f31])).
% 1.28/0.53  fof(f26,plain,(
% 1.28/0.53    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.28/0.53    inference(cnf_transformation,[],[f3])).
% 1.28/0.53  fof(f113,plain,(
% 1.28/0.53    r2_hidden(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl4_3),
% 1.28/0.53    inference(avatar_component_clause,[],[f111])).
% 1.28/0.53  fof(f114,plain,(
% 1.28/0.53    spl4_3 | spl4_1),
% 1.28/0.53    inference(avatar_split_clause,[],[f108,f56,f111])).
% 1.28/0.53  fof(f108,plain,(
% 1.28/0.53    r2_hidden(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl4_1),
% 1.28/0.53    inference(trivial_inequality_removal,[],[f103])).
% 1.28/0.53  fof(f103,plain,(
% 1.28/0.53    r2_hidden(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | spl4_1),
% 1.28/0.53    inference(factoring,[],[f68])).
% 1.28/0.53  fof(f68,plain,(
% 1.28/0.53    ( ! [X1] : (r2_hidden(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,X1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(sK2(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1,X1),X1) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != X1) ) | spl4_1),
% 1.28/0.53    inference(superposition,[],[f58,f39])).
% 1.28/0.53  fof(f39,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0)) )),
% 1.28/0.53    inference(definition_unfolding,[],[f18,f15])).
% 1.28/0.53  fof(f18,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.28/0.53    inference(cnf_transformation,[],[f1])).
% 1.28/0.53  fof(f77,plain,(
% 1.28/0.53    spl4_1 | ~spl4_2),
% 1.28/0.53    inference(avatar_split_clause,[],[f34,f60,f56])).
% 1.28/0.53  fof(f34,plain,(
% 1.28/0.53    ~r2_hidden(sK0,sK1) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.28/0.53    inference(definition_unfolding,[],[f11,f32,f15,f32])).
% 1.28/0.53  fof(f32,plain,(
% 1.28/0.53    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.28/0.53    inference(definition_unfolding,[],[f13,f31])).
% 1.28/0.53  fof(f13,plain,(
% 1.28/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f4])).
% 1.28/0.53  fof(f4,axiom,(
% 1.28/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.28/0.53  fof(f11,plain,(
% 1.28/0.53    ~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.28/0.53    inference(cnf_transformation,[],[f10])).
% 1.28/0.53  fof(f10,plain,(
% 1.28/0.53    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <~> ~r2_hidden(X0,X1))),
% 1.28/0.53    inference(ennf_transformation,[],[f9])).
% 1.28/0.53  fof(f9,negated_conjecture,(
% 1.28/0.53    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.28/0.53    inference(negated_conjecture,[],[f8])).
% 1.28/0.53  fof(f8,conjecture,(
% 1.28/0.53    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 1.28/0.53  fof(f63,plain,(
% 1.28/0.53    ~spl4_1 | spl4_2),
% 1.28/0.53    inference(avatar_split_clause,[],[f33,f60,f56])).
% 1.28/0.53  fof(f33,plain,(
% 1.28/0.53    r2_hidden(sK0,sK1) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.28/0.53    inference(definition_unfolding,[],[f12,f32,f15,f32])).
% 1.28/0.53  fof(f12,plain,(
% 1.28/0.53    r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.28/0.53    inference(cnf_transformation,[],[f10])).
% 1.28/0.53  % SZS output end Proof for theBenchmark
% 1.28/0.53  % (15746)------------------------------
% 1.28/0.53  % (15746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (15746)Termination reason: Refutation
% 1.28/0.53  
% 1.28/0.53  % (15746)Memory used [KB]: 10746
% 1.28/0.53  % (15746)Time elapsed: 0.126 s
% 1.28/0.53  % (15746)------------------------------
% 1.28/0.53  % (15746)------------------------------
% 1.28/0.53  % (15724)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.28/0.53  % (15745)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.28/0.53  % (15717)Success in time 0.173 s
%------------------------------------------------------------------------------
