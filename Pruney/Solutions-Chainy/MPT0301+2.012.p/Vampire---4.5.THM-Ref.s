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
% DateTime   : Thu Dec  3 12:41:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 149 expanded)
%              Number of leaves         :   26 (  67 expanded)
%              Depth                    :    6
%              Number of atoms          :  263 ( 400 expanded)
%              Number of equality atoms :   46 (  82 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f278,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f54,f58,f62,f68,f77,f85,f89,f102,f110,f115,f119,f130,f134,f148,f159,f212,f231,f261,f277])).

fof(f277,plain,
    ( spl9_4
    | ~ spl9_11
    | ~ spl9_24 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | spl9_4
    | ~ spl9_11
    | ~ spl9_24 ),
    inference(subsumption_resolution,[],[f267,f53])).

fof(f53,plain,
    ( k1_xboole_0 != sK0
    | spl9_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl9_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f267,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_11
    | ~ spl9_24 ),
    inference(resolution,[],[f155,f84])).

fof(f84,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl9_11
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK3(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f155,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl9_24
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f261,plain,
    ( spl9_2
    | ~ spl9_11
    | ~ spl9_25 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | spl9_2
    | ~ spl9_11
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f251,f46])).

fof(f46,plain,
    ( k1_xboole_0 != sK1
    | spl9_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl9_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f251,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_11
    | ~ spl9_25 ),
    inference(resolution,[],[f158,f84])).

fof(f158,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl9_25
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f231,plain,
    ( spl9_1
    | ~ spl9_11
    | ~ spl9_31 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | spl9_1
    | ~ spl9_11
    | ~ spl9_31 ),
    inference(unit_resulting_resolution,[],[f43,f211,f84])).

fof(f211,plain,
    ( ! [X2,X3] : ~ r2_hidden(X2,k2_zfmisc_1(X3,k1_xboole_0))
    | ~ spl9_31 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl9_31
  <=> ! [X3,X2] : ~ r2_hidden(X2,k2_zfmisc_1(X3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f43,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl9_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f212,plain,
    ( spl9_31
    | ~ spl9_15
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f145,f132,f100,f210])).

fof(f100,plain,
    ( spl9_15
  <=> ! [X1,X3,X0] :
        ( r2_hidden(sK6(X0,X1,X3),X1)
        | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f132,plain,
    ( spl9_22
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f145,plain,
    ( ! [X2,X3] : ~ r2_hidden(X2,k2_zfmisc_1(X3,k1_xboole_0))
    | ~ spl9_15
    | ~ spl9_22 ),
    inference(resolution,[],[f133,f101])).

fof(f101,plain,
    ( ! [X0,X3,X1] :
        ( r2_hidden(sK6(X0,X1,X3),X1)
        | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) )
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f100])).

fof(f133,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f132])).

fof(f159,plain,
    ( spl9_24
    | spl9_25
    | ~ spl9_7
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f152,f132,f113,f64,f157,f154])).

fof(f64,plain,
    ( spl9_7
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f113,plain,
    ( spl9_18
  <=> ! [X1,X5,X0,X4] :
        ( ~ r2_hidden(X4,X0)
        | ~ r2_hidden(X5,X1)
        | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl9_7
    | ~ spl9_18
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f149,f133])).

fof(f149,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),k1_xboole_0)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl9_7
    | ~ spl9_18 ),
    inference(superposition,[],[f114,f65])).

fof(f65,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f114,plain,
    ( ! [X4,X0,X5,X1] :
        ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
        | ~ r2_hidden(X5,X1)
        | ~ r2_hidden(X4,X0) )
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f113])).

fof(f148,plain,
    ( spl9_3
    | ~ spl9_21
    | ~ spl9_22 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | spl9_3
    | ~ spl9_21
    | ~ spl9_22 ),
    inference(unit_resulting_resolution,[],[f50,f133,f133,f129])).

fof(f129,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK7(X0,X1,X2),X0)
        | r2_hidden(sK4(X0,X1,X2),X2)
        | k2_zfmisc_1(X0,X1) = X2 )
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl9_21
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK7(X0,X1,X2),X0)
        | r2_hidden(sK4(X0,X1,X2),X2)
        | k2_zfmisc_1(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f50,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl9_3
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f134,plain,
    ( spl9_22
    | ~ spl9_6
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f126,f117,f60,f132])).

fof(f60,plain,
    ( spl9_6
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f117,plain,
    ( spl9_19
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | ~ r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f126,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl9_6
    | ~ spl9_19 ),
    inference(resolution,[],[f118,f61])).

fof(f61,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | ~ r2_hidden(X1,X0) )
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f117])).

fof(f130,plain,(
    spl9_21 ),
    inference(avatar_split_clause,[],[f24,f128])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f119,plain,
    ( spl9_19
    | ~ spl9_5
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f111,f108,f56,f117])).

fof(f56,plain,
    ( spl9_5
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f108,plain,
    ( spl9_17
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | ~ r2_hidden(X1,X0) )
    | ~ spl9_5
    | ~ spl9_17 ),
    inference(resolution,[],[f109,f57])).

fof(f57,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f109,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1)
        | ~ r2_hidden(X2,X0) )
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f108])).

fof(f115,plain,(
    spl9_18 ),
    inference(avatar_split_clause,[],[f35,f113])).

fof(f35,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f110,plain,
    ( spl9_17
    | ~ spl9_9
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f90,f87,f75,f108])).

fof(f75,plain,
    ( spl9_9
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f87,plain,
    ( spl9_12
  <=> ! [X1,X0] :
        ( v1_xboole_0(X1)
        | ~ r1_tarski(X1,X0)
        | ~ r1_xboole_0(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f90,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X0) )
    | ~ spl9_9
    | ~ spl9_12 ),
    inference(resolution,[],[f88,f76])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | ~ r2_hidden(X1,X0) )
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f75])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X1)
        | ~ r1_tarski(X1,X0)
        | ~ r1_xboole_0(X1,X0) )
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f87])).

fof(f102,plain,(
    spl9_15 ),
    inference(avatar_split_clause,[],[f37,f100])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f89,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f22,f87])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

% (27783)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f85,plain,(
    spl9_11 ),
    inference(avatar_split_clause,[],[f21,f83])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f77,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f20,f75])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f68,plain,
    ( spl9_7
    | spl9_2
    | spl9_4 ),
    inference(avatar_split_clause,[],[f16,f52,f45,f64])).

fof(f16,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f62,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f18,f60])).

fof(f18,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f58,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f17,f56])).

fof(f17,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f54,plain,
    ( ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f40,f52,f49])).

fof(f40,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(inner_rewriting,[],[f14])).

fof(f14,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f47,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f39,f45,f42])).

fof(f39,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(inner_rewriting,[],[f15])).

fof(f15,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:56:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (27789)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.48  % (27795)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (27787)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (27781)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (27789)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (27781)Refutation not found, incomplete strategy% (27781)------------------------------
% 0.22/0.49  % (27781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (27781)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (27781)Memory used [KB]: 10618
% 0.22/0.49  % (27781)Time elapsed: 0.069 s
% 0.22/0.49  % (27781)------------------------------
% 0.22/0.49  % (27781)------------------------------
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f278,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f47,f54,f58,f62,f68,f77,f85,f89,f102,f110,f115,f119,f130,f134,f148,f159,f212,f231,f261,f277])).
% 0.22/0.49  fof(f277,plain,(
% 0.22/0.49    spl9_4 | ~spl9_11 | ~spl9_24),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f276])).
% 0.22/0.49  fof(f276,plain,(
% 0.22/0.49    $false | (spl9_4 | ~spl9_11 | ~spl9_24)),
% 0.22/0.49    inference(subsumption_resolution,[],[f267,f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    k1_xboole_0 != sK0 | spl9_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    spl9_4 <=> k1_xboole_0 = sK0),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.22/0.49  fof(f267,plain,(
% 0.22/0.49    k1_xboole_0 = sK0 | (~spl9_11 | ~spl9_24)),
% 0.22/0.49    inference(resolution,[],[f155,f84])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) ) | ~spl9_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f83])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    spl9_11 <=> ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl9_24),
% 0.22/0.49    inference(avatar_component_clause,[],[f154])).
% 0.22/0.49  fof(f154,plain,(
% 0.22/0.49    spl9_24 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 0.22/0.49  fof(f261,plain,(
% 0.22/0.49    spl9_2 | ~spl9_11 | ~spl9_25),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f260])).
% 0.22/0.49  fof(f260,plain,(
% 0.22/0.49    $false | (spl9_2 | ~spl9_11 | ~spl9_25)),
% 0.22/0.49    inference(subsumption_resolution,[],[f251,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    k1_xboole_0 != sK1 | spl9_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    spl9_2 <=> k1_xboole_0 = sK1),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.22/0.49  fof(f251,plain,(
% 0.22/0.49    k1_xboole_0 = sK1 | (~spl9_11 | ~spl9_25)),
% 0.22/0.49    inference(resolution,[],[f158,f84])).
% 0.22/0.49  fof(f158,plain,(
% 0.22/0.49    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl9_25),
% 0.22/0.49    inference(avatar_component_clause,[],[f157])).
% 0.22/0.49  fof(f157,plain,(
% 0.22/0.49    spl9_25 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 0.22/0.49  fof(f231,plain,(
% 0.22/0.49    spl9_1 | ~spl9_11 | ~spl9_31),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f219])).
% 0.22/0.49  fof(f219,plain,(
% 0.22/0.49    $false | (spl9_1 | ~spl9_11 | ~spl9_31)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f43,f211,f84])).
% 0.22/0.49  fof(f211,plain,(
% 0.22/0.49    ( ! [X2,X3] : (~r2_hidden(X2,k2_zfmisc_1(X3,k1_xboole_0))) ) | ~spl9_31),
% 0.22/0.49    inference(avatar_component_clause,[],[f210])).
% 0.22/0.49  fof(f210,plain,(
% 0.22/0.49    spl9_31 <=> ! [X3,X2] : ~r2_hidden(X2,k2_zfmisc_1(X3,k1_xboole_0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | spl9_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    spl9_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.49  fof(f212,plain,(
% 0.22/0.49    spl9_31 | ~spl9_15 | ~spl9_22),
% 0.22/0.49    inference(avatar_split_clause,[],[f145,f132,f100,f210])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    spl9_15 <=> ! [X1,X3,X0] : (r2_hidden(sK6(X0,X1,X3),X1) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    spl9_22 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 0.22/0.49  fof(f145,plain,(
% 0.22/0.49    ( ! [X2,X3] : (~r2_hidden(X2,k2_zfmisc_1(X3,k1_xboole_0))) ) | (~spl9_15 | ~spl9_22)),
% 0.22/0.49    inference(resolution,[],[f133,f101])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X1) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) ) | ~spl9_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f100])).
% 0.22/0.49  fof(f133,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl9_22),
% 0.22/0.49    inference(avatar_component_clause,[],[f132])).
% 0.22/0.49  fof(f159,plain,(
% 0.22/0.49    spl9_24 | spl9_25 | ~spl9_7 | ~spl9_18 | ~spl9_22),
% 0.22/0.49    inference(avatar_split_clause,[],[f152,f132,f113,f64,f157,f154])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    spl9_7 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.22/0.49  fof(f113,plain,(
% 0.22/0.49    spl9_18 <=> ! [X1,X5,X0,X4] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.22/0.49  fof(f152,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | (~spl9_7 | ~spl9_18 | ~spl9_22)),
% 0.22/0.49    inference(subsumption_resolution,[],[f149,f133])).
% 0.22/0.49  fof(f149,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k1_xboole_0) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | (~spl9_7 | ~spl9_18)),
% 0.22/0.49    inference(superposition,[],[f114,f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl9_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f64])).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) ) | ~spl9_18),
% 0.22/0.49    inference(avatar_component_clause,[],[f113])).
% 0.22/0.49  fof(f148,plain,(
% 0.22/0.49    spl9_3 | ~spl9_21 | ~spl9_22),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f146])).
% 0.22/0.49  fof(f146,plain,(
% 0.22/0.49    $false | (spl9_3 | ~spl9_21 | ~spl9_22)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f50,f133,f133,f129])).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) ) | ~spl9_21),
% 0.22/0.49    inference(avatar_component_clause,[],[f128])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    spl9_21 <=> ! [X1,X0,X2] : (r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | spl9_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    spl9_3 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    spl9_22 | ~spl9_6 | ~spl9_19),
% 0.22/0.49    inference(avatar_split_clause,[],[f126,f117,f60,f132])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    spl9_6 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.22/0.49  fof(f117,plain,(
% 0.22/0.49    spl9_19 <=> ! [X1,X0] : (~r1_tarski(X0,k1_xboole_0) | ~r2_hidden(X1,X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.22/0.49  fof(f126,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl9_6 | ~spl9_19)),
% 0.22/0.49    inference(resolution,[],[f118,f61])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl9_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f60])).
% 0.22/0.49  fof(f118,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X0,k1_xboole_0) | ~r2_hidden(X1,X0)) ) | ~spl9_19),
% 0.22/0.49    inference(avatar_component_clause,[],[f117])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    spl9_21),
% 0.22/0.49    inference(avatar_split_clause,[],[f24,f128])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    spl9_19 | ~spl9_5 | ~spl9_17),
% 0.22/0.49    inference(avatar_split_clause,[],[f111,f108,f56,f117])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    spl9_5 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    spl9_17 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X0,k1_xboole_0) | ~r2_hidden(X1,X0)) ) | (~spl9_5 | ~spl9_17)),
% 0.22/0.49    inference(resolution,[],[f109,f57])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl9_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f56])).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X0,X1) | ~r2_hidden(X2,X0)) ) | ~spl9_17),
% 0.22/0.49    inference(avatar_component_clause,[],[f108])).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    spl9_18),
% 0.22/0.49    inference(avatar_split_clause,[],[f35,f113])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X4,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))) )),
% 0.22/0.49    inference(equality_resolution,[],[f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.49    inference(equality_resolution,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    spl9_17 | ~spl9_9 | ~spl9_12),
% 0.22/0.49    inference(avatar_split_clause,[],[f90,f87,f75,f108])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    spl9_9 <=> ! [X1,X0] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    spl9_12 <=> ! [X1,X0] : (v1_xboole_0(X1) | ~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) ) | (~spl9_9 | ~spl9_12)),
% 0.22/0.49    inference(resolution,[],[f88,f76])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) ) | ~spl9_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f75])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_xboole_0(X1) | ~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0)) ) | ~spl9_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f87])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    spl9_15),
% 0.22/0.49    inference(avatar_split_clause,[],[f37,f100])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X1) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.49    inference(equality_resolution,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    spl9_12),
% 0.22/0.49    inference(avatar_split_clause,[],[f22,f87])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_xboole_0(X1) | ~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.22/0.49    inference(flattening,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  % (27783)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    spl9_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f21,f83])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    spl9_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f20,f75])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    spl9_7 | spl9_2 | spl9_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f16,f52,f45,f64])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.49    inference(negated_conjecture,[],[f8])).
% 0.22/0.49  fof(f8,conjecture,(
% 0.22/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    spl9_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f18,f60])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    spl9_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f17,f56])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ~spl9_3 | ~spl9_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f40,f52,f49])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.22/0.49    inference(inner_rewriting,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ~spl9_1 | ~spl9_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f39,f45,f42])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.22/0.49    inference(inner_rewriting,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (27789)------------------------------
% 0.22/0.49  % (27789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (27789)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (27789)Memory used [KB]: 10746
% 0.22/0.49  % (27789)Time elapsed: 0.067 s
% 0.22/0.49  % (27789)------------------------------
% 0.22/0.49  % (27789)------------------------------
% 0.22/0.49  % (27779)Success in time 0.127 s
%------------------------------------------------------------------------------
