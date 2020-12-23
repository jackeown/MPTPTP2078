%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:09 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 222 expanded)
%              Number of leaves         :   17 (  66 expanded)
%              Depth                    :   13
%              Number of atoms          :  232 ( 632 expanded)
%              Number of equality atoms :   70 ( 368 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f509,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f85,f90,f97,f324,f504])).

fof(f504,plain,
    ( spl5_1
    | ~ spl5_2
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f503])).

fof(f503,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | spl5_5 ),
    inference(subsumption_resolution,[],[f502,f492])).

fof(f492,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_2
    | spl5_5 ),
    inference(forward_demodulation,[],[f491,f338])).

fof(f338,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | ~ spl5_2 ),
    inference(superposition,[],[f74,f56])).

fof(f56,plain,(
    k2_xboole_0(sK1,sK2) = k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f33,f40])).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f74,plain,
    ( sK1 = k2_tarski(sK0,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl5_2
  <=> sK1 = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f491,plain,
    ( r1_tarski(k2_xboole_0(sK1,sK2),sK2)
    | ~ spl5_2
    | spl5_5 ),
    inference(forward_demodulation,[],[f479,f56])).

fof(f479,plain,
    ( r1_tarski(k2_tarski(sK0,sK0),sK2)
    | ~ spl5_2
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f442,f442,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f442,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_2
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f391,f342])).

fof(f342,plain,
    ( ! [X0] :
        ( r1_xboole_0(sK1,X0)
        | r2_hidden(sK0,X0) )
    | ~ spl5_2 ),
    inference(superposition,[],[f63,f74])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k2_tarski(X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f391,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ spl5_2
    | spl5_5 ),
    inference(superposition,[],[f190,f338])).

fof(f190,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_xboole_0(X0,sK2),sK2)
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f111,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f111,plain,
    ( ! [X0] : ~ r1_xboole_0(sK2,k2_xboole_0(X0,sK2))
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f92,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f92,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f89,f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

% (6268)Refutation not found, incomplete strategy% (6268)------------------------------
% (6268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f5,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

% (6268)Termination reason: Refutation not found, incomplete strategy

fof(f89,plain,
    ( k1_xboole_0 != sK2
    | spl5_5 ),
    inference(avatar_component_clause,[],[f87])).

% (6268)Memory used [KB]: 6140
% (6268)Time elapsed: 0.006 s
fof(f87,plain,
    ( spl5_5
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

% (6268)------------------------------
% (6268)------------------------------
fof(f502,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f388,f71])).

fof(f71,plain,
    ( sK1 != sK2
    | spl5_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl5_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f388,plain,
    ( sK1 = sK2
    | ~ r1_tarski(sK1,sK2)
    | ~ spl5_2 ),
    inference(superposition,[],[f338,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f324,plain,
    ( spl5_3
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f298,f159])).

fof(f159,plain,
    ( r2_hidden(sK3(k1_xboole_0,sK2),k1_xboole_0)
    | spl5_3
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f154,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f154,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | spl5_3
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f132,f44])).

fof(f132,plain,
    ( sK2 != k2_xboole_0(k1_xboole_0,sK2)
    | spl5_3
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f118,f83])).

fof(f83,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f118,plain,
    ( sK2 != k2_xboole_0(sK1,sK2)
    | spl5_3 ),
    inference(superposition,[],[f80,f56])).

fof(f80,plain,
    ( sK2 != k2_tarski(sK0,sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl5_3
  <=> sK2 = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f298,plain,
    ( ~ r2_hidden(sK3(k1_xboole_0,sK2),k1_xboole_0)
    | spl5_3
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f66,f159,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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

fof(f66,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f97,plain,
    ( spl5_2
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | spl5_2
    | spl5_4 ),
    inference(subsumption_resolution,[],[f95,f45])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f95,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | spl5_2
    | spl5_4 ),
    inference(forward_demodulation,[],[f93,f56])).

fof(f93,plain,
    ( ~ r1_tarski(sK1,k2_tarski(sK0,sK0))
    | spl5_2
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f84,f75,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k2_tarski(X1,X1) = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X1)) ) ),
    inference(definition_unfolding,[],[f34,f40,f40])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f75,plain,
    ( sK1 != k2_tarski(sK0,sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f84,plain,
    ( k1_xboole_0 != sK1
    | spl5_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f90,plain,
    ( ~ spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f59,f73,f87])).

fof(f59,plain,
    ( sK1 != k2_tarski(sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f30,f40])).

fof(f30,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f85,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f58,f82,f78])).

fof(f58,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f31,f40])).

fof(f31,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f76,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f67,f73,f69])).

fof(f67,plain,
    ( sK1 != k2_tarski(sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f57])).

fof(f57,plain,
    ( sK1 != k2_tarski(sK0,sK0)
    | sK2 != k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f32,f40,f40])).

fof(f32,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:04:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.37/0.57  % (6253)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.68/0.59  % (6273)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.68/0.60  % (6255)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.68/0.60  % (6272)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.68/0.60  % (6281)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.68/0.60  % (6256)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.68/0.60  % (6265)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.68/0.60  % (6264)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.68/0.60  % (6262)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.68/0.60  % (6258)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.68/0.61  % (6259)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.68/0.62  % (6276)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.68/0.62  % (6257)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.68/0.62  % (6278)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.68/0.62  % (6268)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.68/0.63  % (6262)Refutation found. Thanks to Tanya!
% 1.68/0.63  % SZS status Theorem for theBenchmark
% 1.68/0.63  % SZS output start Proof for theBenchmark
% 1.68/0.63  fof(f509,plain,(
% 1.68/0.63    $false),
% 1.68/0.63    inference(avatar_sat_refutation,[],[f76,f85,f90,f97,f324,f504])).
% 1.68/0.63  fof(f504,plain,(
% 1.68/0.63    spl5_1 | ~spl5_2 | spl5_5),
% 1.68/0.63    inference(avatar_contradiction_clause,[],[f503])).
% 1.68/0.63  fof(f503,plain,(
% 1.68/0.63    $false | (spl5_1 | ~spl5_2 | spl5_5)),
% 1.68/0.63    inference(subsumption_resolution,[],[f502,f492])).
% 1.68/0.63  fof(f492,plain,(
% 1.68/0.63    r1_tarski(sK1,sK2) | (~spl5_2 | spl5_5)),
% 1.68/0.63    inference(forward_demodulation,[],[f491,f338])).
% 1.68/0.63  fof(f338,plain,(
% 1.68/0.63    sK1 = k2_xboole_0(sK1,sK2) | ~spl5_2),
% 1.68/0.63    inference(superposition,[],[f74,f56])).
% 1.68/0.63  fof(f56,plain,(
% 1.68/0.63    k2_xboole_0(sK1,sK2) = k2_tarski(sK0,sK0)),
% 1.68/0.63    inference(definition_unfolding,[],[f33,f40])).
% 1.68/0.63  fof(f40,plain,(
% 1.68/0.63    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.68/0.63    inference(cnf_transformation,[],[f8])).
% 1.68/0.63  fof(f8,axiom,(
% 1.68/0.63    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.68/0.63  fof(f33,plain,(
% 1.68/0.63    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.68/0.63    inference(cnf_transformation,[],[f22])).
% 1.68/0.63  fof(f22,plain,(
% 1.68/0.63    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 1.68/0.63    inference(ennf_transformation,[],[f20])).
% 1.68/0.63  fof(f20,negated_conjecture,(
% 1.68/0.63    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 1.68/0.63    inference(negated_conjecture,[],[f19])).
% 1.68/0.63  fof(f19,conjecture,(
% 1.68/0.63    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.68/0.63  fof(f74,plain,(
% 1.68/0.63    sK1 = k2_tarski(sK0,sK0) | ~spl5_2),
% 1.68/0.63    inference(avatar_component_clause,[],[f73])).
% 1.68/0.63  fof(f73,plain,(
% 1.68/0.63    spl5_2 <=> sK1 = k2_tarski(sK0,sK0)),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.68/0.63  fof(f491,plain,(
% 1.68/0.63    r1_tarski(k2_xboole_0(sK1,sK2),sK2) | (~spl5_2 | spl5_5)),
% 1.68/0.63    inference(forward_demodulation,[],[f479,f56])).
% 1.68/0.63  fof(f479,plain,(
% 1.68/0.63    r1_tarski(k2_tarski(sK0,sK0),sK2) | (~spl5_2 | spl5_5)),
% 1.68/0.63    inference(unit_resulting_resolution,[],[f442,f442,f49])).
% 1.68/0.63  fof(f49,plain,(
% 1.68/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.68/0.63    inference(cnf_transformation,[],[f18])).
% 1.68/0.63  fof(f18,axiom,(
% 1.68/0.63    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.68/0.63  fof(f442,plain,(
% 1.68/0.63    r2_hidden(sK0,sK2) | (~spl5_2 | spl5_5)),
% 1.68/0.63    inference(unit_resulting_resolution,[],[f391,f342])).
% 1.68/0.63  fof(f342,plain,(
% 1.68/0.63    ( ! [X0] : (r1_xboole_0(sK1,X0) | r2_hidden(sK0,X0)) ) | ~spl5_2),
% 1.68/0.63    inference(superposition,[],[f63,f74])).
% 1.68/0.63  fof(f63,plain,(
% 1.68/0.63    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k2_tarski(X0,X0),X1)) )),
% 1.68/0.63    inference(definition_unfolding,[],[f39,f40])).
% 1.68/0.63  fof(f39,plain,(
% 1.68/0.63    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.68/0.63    inference(cnf_transformation,[],[f24])).
% 1.68/0.63  fof(f24,plain,(
% 1.68/0.63    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.68/0.63    inference(ennf_transformation,[],[f15])).
% 1.68/0.63  fof(f15,axiom,(
% 1.68/0.63    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.68/0.63  fof(f391,plain,(
% 1.68/0.63    ~r1_xboole_0(sK1,sK2) | (~spl5_2 | spl5_5)),
% 1.68/0.63    inference(superposition,[],[f190,f338])).
% 1.68/0.63  fof(f190,plain,(
% 1.68/0.63    ( ! [X0] : (~r1_xboole_0(k2_xboole_0(X0,sK2),sK2)) ) | spl5_5),
% 1.68/0.63    inference(unit_resulting_resolution,[],[f111,f46])).
% 1.68/0.63  fof(f46,plain,(
% 1.68/0.63    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.68/0.63    inference(cnf_transformation,[],[f27])).
% 1.68/0.63  fof(f27,plain,(
% 1.68/0.63    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.68/0.63    inference(ennf_transformation,[],[f2])).
% 1.68/0.63  fof(f2,axiom,(
% 1.68/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.68/0.63  fof(f111,plain,(
% 1.68/0.63    ( ! [X0] : (~r1_xboole_0(sK2,k2_xboole_0(X0,sK2))) ) | spl5_5),
% 1.68/0.63    inference(unit_resulting_resolution,[],[f92,f42])).
% 1.68/0.63  fof(f42,plain,(
% 1.68/0.63    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.68/0.63    inference(cnf_transformation,[],[f25])).
% 1.68/0.63  fof(f25,plain,(
% 1.68/0.63    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.68/0.63    inference(ennf_transformation,[],[f6])).
% 1.68/0.63  fof(f6,axiom,(
% 1.68/0.63    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.68/0.63  fof(f92,plain,(
% 1.68/0.63    ~r1_xboole_0(sK2,sK2) | spl5_5),
% 1.68/0.63    inference(unit_resulting_resolution,[],[f89,f37])).
% 1.68/0.63  fof(f37,plain,(
% 1.68/0.63    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_xboole_0(X0,X0)) )),
% 1.68/0.63    inference(cnf_transformation,[],[f23])).
% 1.68/0.63  fof(f23,plain,(
% 1.68/0.63    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.68/0.63    inference(ennf_transformation,[],[f5])).
% 1.68/0.63  % (6268)Refutation not found, incomplete strategy% (6268)------------------------------
% 1.68/0.63  % (6268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.63  fof(f5,axiom,(
% 1.68/0.63    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.68/0.63  % (6268)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.63  
% 1.68/0.63  fof(f89,plain,(
% 1.68/0.63    k1_xboole_0 != sK2 | spl5_5),
% 1.68/0.63    inference(avatar_component_clause,[],[f87])).
% 1.68/0.63  % (6268)Memory used [KB]: 6140
% 1.68/0.63  % (6268)Time elapsed: 0.006 s
% 1.68/0.63  fof(f87,plain,(
% 1.68/0.63    spl5_5 <=> k1_xboole_0 = sK2),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.68/0.63  % (6268)------------------------------
% 1.68/0.63  % (6268)------------------------------
% 1.68/0.63  fof(f502,plain,(
% 1.68/0.63    ~r1_tarski(sK1,sK2) | (spl5_1 | ~spl5_2)),
% 1.68/0.63    inference(subsumption_resolution,[],[f388,f71])).
% 1.68/0.63  fof(f71,plain,(
% 1.68/0.63    sK1 != sK2 | spl5_1),
% 1.68/0.63    inference(avatar_component_clause,[],[f69])).
% 1.68/0.63  fof(f69,plain,(
% 1.68/0.63    spl5_1 <=> sK1 = sK2),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.68/0.63  fof(f388,plain,(
% 1.68/0.63    sK1 = sK2 | ~r1_tarski(sK1,sK2) | ~spl5_2),
% 1.68/0.63    inference(superposition,[],[f338,f44])).
% 1.68/0.63  fof(f44,plain,(
% 1.68/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.68/0.63    inference(cnf_transformation,[],[f26])).
% 1.68/0.63  fof(f26,plain,(
% 1.68/0.63    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.68/0.63    inference(ennf_transformation,[],[f4])).
% 1.68/0.63  fof(f4,axiom,(
% 1.68/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.68/0.63  fof(f324,plain,(
% 1.68/0.63    spl5_3 | ~spl5_4),
% 1.68/0.63    inference(avatar_contradiction_clause,[],[f323])).
% 1.68/0.63  fof(f323,plain,(
% 1.68/0.63    $false | (spl5_3 | ~spl5_4)),
% 1.68/0.63    inference(subsumption_resolution,[],[f298,f159])).
% 1.68/0.63  fof(f159,plain,(
% 1.68/0.63    r2_hidden(sK3(k1_xboole_0,sK2),k1_xboole_0) | (spl5_3 | ~spl5_4)),
% 1.68/0.63    inference(unit_resulting_resolution,[],[f154,f51])).
% 1.68/0.63  fof(f51,plain,(
% 1.68/0.63    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.68/0.63    inference(cnf_transformation,[],[f28])).
% 1.68/0.63  fof(f28,plain,(
% 1.68/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.68/0.63    inference(ennf_transformation,[],[f1])).
% 1.68/0.63  fof(f1,axiom,(
% 1.68/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.68/0.63  fof(f154,plain,(
% 1.68/0.63    ~r1_tarski(k1_xboole_0,sK2) | (spl5_3 | ~spl5_4)),
% 1.68/0.63    inference(unit_resulting_resolution,[],[f132,f44])).
% 1.68/0.63  fof(f132,plain,(
% 1.68/0.63    sK2 != k2_xboole_0(k1_xboole_0,sK2) | (spl5_3 | ~spl5_4)),
% 1.68/0.63    inference(forward_demodulation,[],[f118,f83])).
% 1.68/0.63  fof(f83,plain,(
% 1.68/0.63    k1_xboole_0 = sK1 | ~spl5_4),
% 1.68/0.63    inference(avatar_component_clause,[],[f82])).
% 1.68/0.63  fof(f82,plain,(
% 1.68/0.63    spl5_4 <=> k1_xboole_0 = sK1),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.68/0.63  fof(f118,plain,(
% 1.68/0.63    sK2 != k2_xboole_0(sK1,sK2) | spl5_3),
% 1.68/0.63    inference(superposition,[],[f80,f56])).
% 1.68/0.63  fof(f80,plain,(
% 1.68/0.63    sK2 != k2_tarski(sK0,sK0) | spl5_3),
% 1.68/0.63    inference(avatar_component_clause,[],[f78])).
% 1.68/0.63  fof(f78,plain,(
% 1.68/0.63    spl5_3 <=> sK2 = k2_tarski(sK0,sK0)),
% 1.68/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.68/0.63  fof(f298,plain,(
% 1.68/0.63    ~r2_hidden(sK3(k1_xboole_0,sK2),k1_xboole_0) | (spl5_3 | ~spl5_4)),
% 1.68/0.63    inference(unit_resulting_resolution,[],[f66,f159,f53])).
% 1.68/0.63  fof(f53,plain,(
% 1.68/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 1.68/0.63    inference(cnf_transformation,[],[f29])).
% 1.68/0.63  fof(f29,plain,(
% 1.68/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.68/0.63    inference(ennf_transformation,[],[f21])).
% 1.68/0.63  fof(f21,plain,(
% 1.68/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.68/0.63    inference(rectify,[],[f3])).
% 1.68/0.63  fof(f3,axiom,(
% 1.68/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.68/0.63  fof(f66,plain,(
% 1.68/0.63    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.68/0.63    inference(equality_resolution,[],[f38])).
% 1.68/0.63  fof(f38,plain,(
% 1.68/0.63    ( ! [X0] : (r1_xboole_0(X0,X0) | k1_xboole_0 != X0) )),
% 1.68/0.63    inference(cnf_transformation,[],[f23])).
% 1.68/0.63  fof(f97,plain,(
% 1.68/0.63    spl5_2 | spl5_4),
% 1.68/0.63    inference(avatar_contradiction_clause,[],[f96])).
% 1.68/0.63  fof(f96,plain,(
% 1.68/0.63    $false | (spl5_2 | spl5_4)),
% 1.68/0.63    inference(subsumption_resolution,[],[f95,f45])).
% 1.68/0.63  fof(f45,plain,(
% 1.68/0.63    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.68/0.63    inference(cnf_transformation,[],[f7])).
% 1.68/0.63  fof(f7,axiom,(
% 1.68/0.63    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.68/0.63  fof(f95,plain,(
% 1.68/0.63    ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | (spl5_2 | spl5_4)),
% 1.68/0.63    inference(forward_demodulation,[],[f93,f56])).
% 1.68/0.63  fof(f93,plain,(
% 1.68/0.63    ~r1_tarski(sK1,k2_tarski(sK0,sK0)) | (spl5_2 | spl5_4)),
% 1.68/0.63    inference(unit_resulting_resolution,[],[f84,f75,f62])).
% 1.68/0.63  fof(f62,plain,(
% 1.68/0.63    ( ! [X0,X1] : (k1_xboole_0 = X0 | k2_tarski(X1,X1) = X0 | ~r1_tarski(X0,k2_tarski(X1,X1))) )),
% 1.68/0.63    inference(definition_unfolding,[],[f34,f40,f40])).
% 1.68/0.63  fof(f34,plain,(
% 1.68/0.63    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.68/0.63    inference(cnf_transformation,[],[f16])).
% 1.68/0.63  fof(f16,axiom,(
% 1.68/0.63    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.68/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.68/0.63  fof(f75,plain,(
% 1.68/0.63    sK1 != k2_tarski(sK0,sK0) | spl5_2),
% 1.68/0.63    inference(avatar_component_clause,[],[f73])).
% 1.68/0.63  fof(f84,plain,(
% 1.68/0.63    k1_xboole_0 != sK1 | spl5_4),
% 1.68/0.63    inference(avatar_component_clause,[],[f82])).
% 1.68/0.63  fof(f90,plain,(
% 1.68/0.63    ~spl5_5 | ~spl5_2),
% 1.68/0.63    inference(avatar_split_clause,[],[f59,f73,f87])).
% 1.68/0.63  fof(f59,plain,(
% 1.68/0.63    sK1 != k2_tarski(sK0,sK0) | k1_xboole_0 != sK2),
% 1.68/0.63    inference(definition_unfolding,[],[f30,f40])).
% 1.68/0.63  fof(f30,plain,(
% 1.68/0.63    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 1.68/0.63    inference(cnf_transformation,[],[f22])).
% 1.68/0.63  fof(f85,plain,(
% 1.68/0.63    ~spl5_3 | ~spl5_4),
% 1.68/0.63    inference(avatar_split_clause,[],[f58,f82,f78])).
% 1.68/0.63  fof(f58,plain,(
% 1.68/0.63    k1_xboole_0 != sK1 | sK2 != k2_tarski(sK0,sK0)),
% 1.68/0.63    inference(definition_unfolding,[],[f31,f40])).
% 1.68/0.63  fof(f31,plain,(
% 1.68/0.63    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 1.68/0.63    inference(cnf_transformation,[],[f22])).
% 1.68/0.63  fof(f76,plain,(
% 1.68/0.63    ~spl5_1 | ~spl5_2),
% 1.68/0.63    inference(avatar_split_clause,[],[f67,f73,f69])).
% 1.68/0.63  fof(f67,plain,(
% 1.68/0.63    sK1 != k2_tarski(sK0,sK0) | sK1 != sK2),
% 1.68/0.63    inference(inner_rewriting,[],[f57])).
% 1.68/0.63  fof(f57,plain,(
% 1.68/0.63    sK1 != k2_tarski(sK0,sK0) | sK2 != k2_tarski(sK0,sK0)),
% 1.68/0.63    inference(definition_unfolding,[],[f32,f40,f40])).
% 1.68/0.63  fof(f32,plain,(
% 1.68/0.63    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 1.68/0.63    inference(cnf_transformation,[],[f22])).
% 1.68/0.63  % SZS output end Proof for theBenchmark
% 1.68/0.63  % (6262)------------------------------
% 1.68/0.63  % (6262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.63  % (6262)Termination reason: Refutation
% 1.68/0.63  
% 1.68/0.63  % (6262)Memory used [KB]: 10874
% 1.68/0.63  % (6262)Time elapsed: 0.199 s
% 1.68/0.63  % (6262)------------------------------
% 1.68/0.63  % (6262)------------------------------
% 1.68/0.63  % (6261)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.68/0.63  % (6282)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.68/0.63  % (6267)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.68/0.64  % (6277)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.68/0.64  % (6260)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.68/0.64  % (6270)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.68/0.65  % (6275)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.68/0.65  % (6279)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.68/0.65  % (6254)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.68/0.65  % (6252)Success in time 0.292 s
%------------------------------------------------------------------------------
