%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 112 expanded)
%              Number of leaves         :   15 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :  174 ( 278 expanded)
%              Number of equality atoms :   61 ( 109 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f159,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f66,f71,f93,f104,f127,f136,f157,f158])).

fof(f158,plain,
    ( sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2))
    | r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK2))
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2)),k2_enumset1(sK0,sK0,sK0,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f157,plain,
    ( ~ spl5_1
    | ~ spl5_11
    | spl5_3
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f147,f101,f68,f154,f58])).

fof(f58,plain,
    ( spl5_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f154,plain,
    ( spl5_11
  <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f68,plain,
    ( spl5_3
  <=> k2_enumset1(sK0,sK0,sK0,sK2) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK2),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f101,plain,
    ( spl5_8
  <=> sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f147,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK2))
    | ~ r2_hidden(sK0,sK1)
    | spl5_3
    | ~ spl5_8 ),
    inference(trivial_inequality_removal,[],[f146])).

fof(f146,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK2))
    | ~ r2_hidden(sK0,sK1)
    | k2_enumset1(sK0,sK0,sK0,sK2) != k2_enumset1(sK0,sK0,sK0,sK2)
    | spl5_3
    | ~ spl5_8 ),
    inference(duplicate_literal_removal,[],[f139])).

fof(f139,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK2))
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK2))
    | k2_enumset1(sK0,sK0,sK0,sK2) != k2_enumset1(sK0,sK0,sK0,sK2)
    | spl5_3
    | ~ spl5_8 ),
    inference(superposition,[],[f72,f103])).

fof(f103,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f72,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),k2_enumset1(sK0,sK0,sK0,sK2))
        | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),sK1)
        | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),X0)
        | k2_enumset1(sK0,sK0,sK0,sK2) != X0 )
    | spl5_3 ),
    inference(superposition,[],[f70,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f17,f15])).

fof(f15,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f70,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK2) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK2),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK2),sK1))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f136,plain,(
    spl5_9 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | spl5_9 ),
    inference(unit_resulting_resolution,[],[f51,f126])).

fof(f126,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK2))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl5_9
  <=> r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f51,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k2_enumset1(X0,X0,X1,X4)) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f30,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f127,plain,
    ( ~ spl5_2
    | ~ spl5_9
    | spl5_3
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f119,f97,f68,f124,f63])).

fof(f63,plain,
    ( spl5_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f97,plain,
    ( spl5_7
  <=> sK2 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f119,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK2))
    | ~ r2_hidden(sK2,sK1)
    | spl5_3
    | ~ spl5_7 ),
    inference(trivial_inequality_removal,[],[f118])).

fof(f118,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK2))
    | ~ r2_hidden(sK2,sK1)
    | k2_enumset1(sK0,sK0,sK0,sK2) != k2_enumset1(sK0,sK0,sK0,sK2)
    | spl5_3
    | ~ spl5_7 ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK2))
    | ~ r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK2))
    | k2_enumset1(sK0,sK0,sK0,sK2) != k2_enumset1(sK0,sK0,sK0,sK2)
    | spl5_3
    | ~ spl5_7 ),
    inference(superposition,[],[f72,f99])).

fof(f99,plain,
    ( sK2 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f97])).

fof(f104,plain,
    ( spl5_7
    | spl5_8
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f95,f90,f101,f97])).

fof(f90,plain,
    ( spl5_6
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2)),k2_enumset1(sK0,sK0,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f95,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2))
    | sK2 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2))
    | ~ spl5_6 ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2))
    | sK2 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2))
    | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2))
    | ~ spl5_6 ),
    inference(resolution,[],[f92,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f27,f16])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f92,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2)),k2_enumset1(sK0,sK0,sK0,sK2))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f93,plain,
    ( spl5_6
    | spl5_3 ),
    inference(avatar_split_clause,[],[f87,f68,f90])).

fof(f87,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2)),k2_enumset1(sK0,sK0,sK0,sK2))
    | spl5_3 ),
    inference(trivial_inequality_removal,[],[f86])).

fof(f86,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2)),k2_enumset1(sK0,sK0,sK0,sK2))
    | k2_enumset1(sK0,sK0,sK0,sK2) != k2_enumset1(sK0,sK0,sK0,sK2)
    | spl5_3 ),
    inference(factoring,[],[f73])).

fof(f73,plain,
    ( ! [X1] :
        ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X1),k2_enumset1(sK0,sK0,sK0,sK2))
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X1),X1)
        | k2_enumset1(sK0,sK0,sK0,sK2) != X1 )
    | spl5_3 ),
    inference(superposition,[],[f70,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f18,f15])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f71,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f32,f68])).

fof(f32,plain,(
    k2_enumset1(sK0,sK0,sK0,sK2) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK2),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK2),sK1)) ),
    inference(definition_unfolding,[],[f13,f31,f15,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f14,f16])).

fof(f14,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f13,plain,(
    k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f8])).

% (4509)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(f66,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f12,f63])).

fof(f12,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f61,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f11,f58])).

fof(f11,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:26:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (4527)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (4510)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (4519)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (4511)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (4514)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (4508)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (4506)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (4506)Refutation not found, incomplete strategy% (4506)------------------------------
% 0.21/0.53  % (4506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4506)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4506)Memory used [KB]: 10618
% 0.21/0.53  % (4506)Time elapsed: 0.105 s
% 0.21/0.53  % (4506)------------------------------
% 0.21/0.53  % (4506)------------------------------
% 0.21/0.53  % (4526)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (4518)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (4526)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f159,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f61,f66,f71,f93,f104,f127,f136,f157,f158])).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2)) | r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK2)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2)),k2_enumset1(sK0,sK0,sK0,sK2))),
% 0.21/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    ~spl5_1 | ~spl5_11 | spl5_3 | ~spl5_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f147,f101,f68,f154,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    spl5_1 <=> r2_hidden(sK0,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.54  fof(f154,plain,(
% 0.21/0.54    spl5_11 <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    spl5_3 <=> k2_enumset1(sK0,sK0,sK0,sK2) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK2),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK2),sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    spl5_8 <=> sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.54  fof(f147,plain,(
% 0.21/0.54    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK2)) | ~r2_hidden(sK0,sK1) | (spl5_3 | ~spl5_8)),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f146])).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK2)) | ~r2_hidden(sK0,sK1) | k2_enumset1(sK0,sK0,sK0,sK2) != k2_enumset1(sK0,sK0,sK0,sK2) | (spl5_3 | ~spl5_8)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f139])).
% 0.21/0.54  fof(f139,plain,(
% 0.21/0.54    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK2)) | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK2)) | k2_enumset1(sK0,sK0,sK0,sK2) != k2_enumset1(sK0,sK0,sK0,sK2) | (spl5_3 | ~spl5_8)),
% 0.21/0.54    inference(superposition,[],[f72,f103])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2)) | ~spl5_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f101])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),k2_enumset1(sK0,sK0,sK0,sK2)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),sK1) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),X0) | k2_enumset1(sK0,sK0,sK0,sK2) != X0) ) | spl5_3),
% 0.21/0.54    inference(superposition,[],[f70,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f17,f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    k2_enumset1(sK0,sK0,sK0,sK2) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK2),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK2),sK1)) | spl5_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f68])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    spl5_9),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f133])).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    $false | spl5_9),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f51,f126])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    ~r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK2)) | spl5_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f124])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    spl5_9 <=> r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_enumset1(X0,X0,X1,X4))) )),
% 0.21/0.54    inference(equality_resolution,[],[f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X4) != X3) )),
% 0.21/0.54    inference(equality_resolution,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.21/0.54    inference(definition_unfolding,[],[f30,f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    ~spl5_2 | ~spl5_9 | spl5_3 | ~spl5_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f119,f97,f68,f124,f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    spl5_2 <=> r2_hidden(sK2,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    spl5_7 <=> sK2 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    ~r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK2)) | ~r2_hidden(sK2,sK1) | (spl5_3 | ~spl5_7)),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f118])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    ~r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK2)) | ~r2_hidden(sK2,sK1) | k2_enumset1(sK0,sK0,sK0,sK2) != k2_enumset1(sK0,sK0,sK0,sK2) | (spl5_3 | ~spl5_7)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f117])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    ~r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK2)) | ~r2_hidden(sK2,sK1) | ~r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK2)) | k2_enumset1(sK0,sK0,sK0,sK2) != k2_enumset1(sK0,sK0,sK0,sK2) | (spl5_3 | ~spl5_7)),
% 0.21/0.54    inference(superposition,[],[f72,f99])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    sK2 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2)) | ~spl5_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f97])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    spl5_7 | spl5_8 | ~spl5_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f95,f90,f101,f97])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    spl5_6 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2)),k2_enumset1(sK0,sK0,sK0,sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2)) | sK2 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2)) | ~spl5_6),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f94])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2)) | sK2 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2)) | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2)) | ~spl5_6),
% 0.21/0.54    inference(resolution,[],[f92,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 0.21/0.54    inference(equality_resolution,[],[f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.21/0.54    inference(definition_unfolding,[],[f27,f16])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2)),k2_enumset1(sK0,sK0,sK0,sK2)) | ~spl5_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f90])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    spl5_6 | spl5_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f87,f68,f90])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2)),k2_enumset1(sK0,sK0,sK0,sK2)) | spl5_3),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f86])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK2)),k2_enumset1(sK0,sK0,sK0,sK2)) | k2_enumset1(sK0,sK0,sK0,sK2) != k2_enumset1(sK0,sK0,sK0,sK2) | spl5_3),
% 0.21/0.54    inference(factoring,[],[f73])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X1] : (r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X1),k2_enumset1(sK0,sK0,sK0,sK2)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X1),X1) | k2_enumset1(sK0,sK0,sK0,sK2) != X1) ) | spl5_3),
% 0.21/0.54    inference(superposition,[],[f70,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f18,f15])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ~spl5_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f32,f68])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    k2_enumset1(sK0,sK0,sK0,sK2) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK2),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK2),sK1))),
% 0.21/0.54    inference(definition_unfolding,[],[f13,f31,f15,f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f14,f16])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1) & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f8])).
% 0.21/0.54  % (4509)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  fof(f8,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1) & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 0.21/0.54    inference(negated_conjecture,[],[f6])).
% 0.21/0.54  fof(f6,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    spl5_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f12,f63])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    r2_hidden(sK2,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    spl5_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f11,f58])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    r2_hidden(sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (4526)------------------------------
% 0.21/0.54  % (4526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4526)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (4526)Memory used [KB]: 10746
% 0.21/0.54  % (4526)Time elapsed: 0.117 s
% 0.21/0.54  % (4526)------------------------------
% 0.21/0.54  % (4526)------------------------------
% 0.21/0.54  % (4503)Success in time 0.175 s
%------------------------------------------------------------------------------
