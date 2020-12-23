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
% DateTime   : Thu Dec  3 12:41:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 186 expanded)
%              Number of leaves         :   27 (  74 expanded)
%              Depth                    :   11
%              Number of atoms          :  224 ( 400 expanded)
%              Number of equality atoms :   42 (  95 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f336,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f76,f81,f86,f207,f213,f232,f267,f285,f292,f295,f314,f325,f332,f334,f335])).

fof(f335,plain,
    ( sK0 != k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ r1_tarski(sK1,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | r1_tarski(sK1,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

% (18410)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% (18406)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% (18394)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% (18401)Refutation not found, incomplete strategy% (18401)------------------------------
% (18401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18401)Termination reason: Refutation not found, incomplete strategy

% (18401)Memory used [KB]: 10618
% (18401)Time elapsed: 0.145 s
% (18401)------------------------------
% (18401)------------------------------
% (18411)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% (18412)Refutation not found, incomplete strategy% (18412)------------------------------
% (18412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18412)Termination reason: Refutation not found, incomplete strategy

% (18412)Memory used [KB]: 6268
% (18412)Time elapsed: 0.160 s
% (18412)------------------------------
% (18412)------------------------------
fof(f334,plain,
    ( sK1 != k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | r1_tarski(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f332,plain,(
    spl5_22 ),
    inference(avatar_contradiction_clause,[],[f326])).

fof(f326,plain,
    ( $false
    | spl5_22 ),
    inference(unit_resulting_resolution,[],[f48,f324])).

fof(f324,plain,
    ( ~ r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | spl5_22 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl5_22
  <=> r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f17,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f17,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

% (18403)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
fof(f325,plain,
    ( spl5_21
    | ~ spl5_22
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f315,f311,f322,f318])).

fof(f318,plain,
    ( spl5_21
  <=> sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f311,plain,
    ( spl5_20
  <=> r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f315,plain,
    ( ~ r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ spl5_20 ),
    inference(resolution,[],[f313,f23])).

fof(f23,plain,(
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

fof(f313,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK0)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f311])).

fof(f314,plain,
    ( spl5_20
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f309,f229,f311])).

fof(f229,plain,
    ( spl5_16
  <=> r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f309,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK0)
    | ~ spl5_16 ),
    inference(resolution,[],[f231,f53])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f231,plain,
    ( r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f229])).

fof(f295,plain,(
    spl5_19 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | spl5_19 ),
    inference(unit_resulting_resolution,[],[f52,f291,f54])).

fof(f54,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f291,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK1))
    | spl5_19 ),
    inference(avatar_component_clause,[],[f289])).

fof(f289,plain,
    ( spl5_19
  <=> r2_hidden(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f292,plain,
    ( ~ spl5_19
    | ~ spl5_4
    | spl5_18 ),
    inference(avatar_split_clause,[],[f287,f282,f83,f289])).

fof(f83,plain,
    ( spl5_4
  <=> k3_tarski(k1_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))) = k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f282,plain,
    ( spl5_18
  <=> r1_tarski(sK1,k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f287,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK1))
    | ~ spl5_4
    | spl5_18 ),
    inference(resolution,[],[f284,f185])).

fof(f185,plain,
    ( ! [X2] :
        ( r1_tarski(X2,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
        | ~ r2_hidden(X2,k1_zfmisc_1(sK1)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f134,f53])).

fof(f134,plain,
    ( ! [X6] :
        ( r2_hidden(X6,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))
        | ~ r2_hidden(X6,k1_zfmisc_1(sK1)) )
    | ~ spl5_4 ),
    inference(condensation,[],[f130])).

fof(f130,plain,
    ( ! [X6,X7] :
        ( r2_hidden(X6,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))
        | ~ r2_hidden(X6,X7)
        | ~ r2_hidden(X6,k1_zfmisc_1(sK1)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f97,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
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

fof(f97,plain,
    ( ! [X4,X5] :
        ( r2_hidden(X5,k4_xboole_0(k4_xboole_0(X4,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK1)))
        | r2_hidden(X5,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))
        | ~ r2_hidden(X5,X4) )
    | ~ spl5_4 ),
    inference(superposition,[],[f55,f87])).

fof(f87,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(X0,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK1)) = k4_xboole_0(X0,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))
    | ~ spl5_4 ),
    inference(superposition,[],[f50,f85])).

fof(f85,plain,
    ( k3_tarski(k1_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))) = k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f50,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(definition_unfolding,[],[f31,f46])).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f284,plain,
    ( ~ r1_tarski(sK1,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | spl5_18 ),
    inference(avatar_component_clause,[],[f282])).

fof(f285,plain,
    ( spl5_17
    | ~ spl5_18
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f268,f210,f282,f278])).

fof(f278,plain,
    ( spl5_17
  <=> sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f210,plain,
    ( spl5_14
  <=> r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f268,plain,
    ( ~ r1_tarski(sK1,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ spl5_14 ),
    inference(resolution,[],[f212,f23])).

fof(f212,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK1)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f210])).

fof(f267,plain,(
    ~ spl5_15 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f59,f227,f227,f55])).

fof(f227,plain,
    ( ! [X0] : ~ r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),X0)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl5_15
  <=> ! [X0] : ~ r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f59,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k1_enumset1(X0,X1,X4)) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f232,plain,
    ( spl5_15
    | spl5_16
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f224,f205,f229,f226])).

fof(f205,plain,
    ( spl5_13
  <=> ! [X1] : ~ r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k4_xboole_0(X1,k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f224,plain,
    ( ! [X0] :
        ( r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK0))
        | ~ r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),X0) )
    | ~ spl5_13 ),
    inference(resolution,[],[f206,f55])).

fof(f206,plain,
    ( ! [X1] : ~ r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k4_xboole_0(X1,k1_zfmisc_1(sK0)))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f205])).

fof(f213,plain,
    ( spl5_14
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f208,f201,f210])).

fof(f201,plain,
    ( spl5_12
  <=> r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f208,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK1)
    | ~ spl5_12 ),
    inference(resolution,[],[f203,f53])).

fof(f203,plain,
    ( r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f201])).

fof(f207,plain,
    ( spl5_12
    | spl5_13
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f124,f83,f205,f201])).

fof(f124,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k4_xboole_0(X1,k1_zfmisc_1(sK0)))
        | r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK1)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f117,f52])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_zfmisc_1(sK0)))
        | r2_hidden(X0,k1_zfmisc_1(sK1)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f103,f54])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))
        | r2_hidden(X0,k1_zfmisc_1(sK1))
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_zfmisc_1(sK0))) )
    | ~ spl5_4 ),
    inference(resolution,[],[f96,f55])).

fof(f96,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k4_xboole_0(k4_xboole_0(X2,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK1)))
        | ~ r2_hidden(X3,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))) )
    | ~ spl5_4 ),
    inference(superposition,[],[f56,f87])).

fof(f86,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f47,f83])).

fof(f47,plain,(
    k3_tarski(k1_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))) = k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f15,f46,f46])).

fof(f15,plain,(
    k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ~ r3_xboole_0(X0,X1)
      & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1))
       => r3_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1))
     => r3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_zfmisc_1)).

fof(f81,plain,
    ( ~ spl5_3
    | spl5_1 ),
    inference(avatar_split_clause,[],[f71,f66,f78])).

fof(f78,plain,
    ( spl5_3
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f66,plain,
    ( spl5_1
  <=> r3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f71,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl5_1 ),
    inference(resolution,[],[f68,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).

fof(f68,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f76,plain,
    ( ~ spl5_2
    | spl5_1 ),
    inference(avatar_split_clause,[],[f70,f66,f73])).

fof(f73,plain,
    ( spl5_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f70,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl5_1 ),
    inference(resolution,[],[f68,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f69,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f16,f66])).

fof(f16,plain,(
    ~ r3_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:27:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (18388)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (18404)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.51  % (18384)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (18398)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (18389)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (18392)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (18385)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (18385)Refutation not found, incomplete strategy% (18385)------------------------------
% 0.21/0.52  % (18385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18385)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (18385)Memory used [KB]: 1663
% 0.21/0.52  % (18385)Time elapsed: 0.107 s
% 0.21/0.52  % (18385)------------------------------
% 0.21/0.52  % (18385)------------------------------
% 0.21/0.53  % (18415)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (18399)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (18407)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (18387)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (18386)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (18408)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (18391)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (18415)Refutation not found, incomplete strategy% (18415)------------------------------
% 0.21/0.54  % (18415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18402)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (18413)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (18405)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (18400)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (18412)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (18397)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (18415)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (18415)Memory used [KB]: 1663
% 0.21/0.54  % (18415)Time elapsed: 0.095 s
% 0.21/0.54  % (18415)------------------------------
% 0.21/0.54  % (18415)------------------------------
% 0.21/0.55  % (18401)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (18409)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (18399)Refutation not found, incomplete strategy% (18399)------------------------------
% 0.21/0.55  % (18399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (18399)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (18399)Memory used [KB]: 1791
% 0.21/0.55  % (18399)Time elapsed: 0.106 s
% 0.21/0.55  % (18399)------------------------------
% 0.21/0.55  % (18399)------------------------------
% 0.21/0.55  % (18390)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (18395)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (18413)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f336,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f69,f76,f81,f86,f207,f213,f232,f267,f285,f292,f295,f314,f325,f332,f334,f335])).
% 0.21/0.55  fof(f335,plain,(
% 0.21/0.55    sK0 != k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~r1_tarski(sK1,k3_tarski(k1_enumset1(sK0,sK0,sK1))) | r1_tarski(sK1,sK0)),
% 0.21/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.56  % (18410)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.56  % (18406)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.56  % (18394)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (18401)Refutation not found, incomplete strategy% (18401)------------------------------
% 0.21/0.56  % (18401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (18401)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (18401)Memory used [KB]: 10618
% 0.21/0.56  % (18401)Time elapsed: 0.145 s
% 0.21/0.56  % (18401)------------------------------
% 0.21/0.56  % (18401)------------------------------
% 0.21/0.56  % (18411)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (18412)Refutation not found, incomplete strategy% (18412)------------------------------
% 0.21/0.57  % (18412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (18412)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (18412)Memory used [KB]: 6268
% 0.21/0.57  % (18412)Time elapsed: 0.160 s
% 0.21/0.57  % (18412)------------------------------
% 0.21/0.57  % (18412)------------------------------
% 0.21/0.57  fof(f334,plain,(
% 0.21/0.57    sK1 != k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1))) | r1_tarski(sK0,sK1)),
% 0.21/0.57    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.57  fof(f332,plain,(
% 0.21/0.57    spl5_22),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f326])).
% 0.21/0.57  fof(f326,plain,(
% 0.21/0.57    $false | spl5_22),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f48,f324])).
% 0.21/0.57  fof(f324,plain,(
% 0.21/0.57    ~r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1))) | spl5_22),
% 0.21/0.57    inference(avatar_component_clause,[],[f322])).
% 0.21/0.57  fof(f322,plain,(
% 0.21/0.57    spl5_22 <=> r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f17,f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f20,f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.57  % (18403)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.57  fof(f325,plain,(
% 0.21/0.57    spl5_21 | ~spl5_22 | ~spl5_20),
% 0.21/0.57    inference(avatar_split_clause,[],[f315,f311,f322,f318])).
% 0.21/0.57  fof(f318,plain,(
% 0.21/0.57    spl5_21 <=> sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.57  fof(f311,plain,(
% 0.21/0.57    spl5_20 <=> r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.57  fof(f315,plain,(
% 0.21/0.57    ~r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1))) | sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~spl5_20),
% 0.21/0.57    inference(resolution,[],[f313,f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.57  fof(f313,plain,(
% 0.21/0.57    r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK0) | ~spl5_20),
% 0.21/0.57    inference(avatar_component_clause,[],[f311])).
% 0.21/0.57  fof(f314,plain,(
% 0.21/0.57    spl5_20 | ~spl5_16),
% 0.21/0.57    inference(avatar_split_clause,[],[f309,f229,f311])).
% 0.21/0.57  fof(f229,plain,(
% 0.21/0.57    spl5_16 <=> r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.57  fof(f309,plain,(
% 0.21/0.57    r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK0) | ~spl5_16),
% 0.21/0.57    inference(resolution,[],[f231,f53])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 0.21/0.57    inference(equality_resolution,[],[f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.57  fof(f231,plain,(
% 0.21/0.57    r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK0)) | ~spl5_16),
% 0.21/0.57    inference(avatar_component_clause,[],[f229])).
% 0.21/0.57  fof(f295,plain,(
% 0.21/0.57    spl5_19),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f293])).
% 0.21/0.57  fof(f293,plain,(
% 0.21/0.57    $false | spl5_19),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f52,f291,f54])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 0.21/0.57    inference(equality_resolution,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f9])).
% 0.21/0.57  fof(f291,plain,(
% 0.21/0.57    ~r2_hidden(sK1,k1_zfmisc_1(sK1)) | spl5_19),
% 0.21/0.57    inference(avatar_component_clause,[],[f289])).
% 0.21/0.57  fof(f289,plain,(
% 0.21/0.57    spl5_19 <=> r2_hidden(sK1,k1_zfmisc_1(sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.57    inference(equality_resolution,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f292,plain,(
% 0.21/0.57    ~spl5_19 | ~spl5_4 | spl5_18),
% 0.21/0.57    inference(avatar_split_clause,[],[f287,f282,f83,f289])).
% 0.21/0.57  fof(f83,plain,(
% 0.21/0.57    spl5_4 <=> k3_tarski(k1_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))) = k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.57  fof(f282,plain,(
% 0.21/0.57    spl5_18 <=> r1_tarski(sK1,k3_tarski(k1_enumset1(sK0,sK0,sK1)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.57  fof(f287,plain,(
% 0.21/0.57    ~r2_hidden(sK1,k1_zfmisc_1(sK1)) | (~spl5_4 | spl5_18)),
% 0.21/0.57    inference(resolution,[],[f284,f185])).
% 0.21/0.57  fof(f185,plain,(
% 0.21/0.57    ( ! [X2] : (r1_tarski(X2,k3_tarski(k1_enumset1(sK0,sK0,sK1))) | ~r2_hidden(X2,k1_zfmisc_1(sK1))) ) | ~spl5_4),
% 0.21/0.57    inference(resolution,[],[f134,f53])).
% 0.21/0.57  fof(f134,plain,(
% 0.21/0.57    ( ! [X6] : (r2_hidden(X6,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))) | ~r2_hidden(X6,k1_zfmisc_1(sK1))) ) | ~spl5_4),
% 0.21/0.57    inference(condensation,[],[f130])).
% 0.21/0.57  fof(f130,plain,(
% 0.21/0.57    ( ! [X6,X7] : (r2_hidden(X6,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))) | ~r2_hidden(X6,X7) | ~r2_hidden(X6,k1_zfmisc_1(sK1))) ) | ~spl5_4),
% 0.21/0.57    inference(resolution,[],[f97,f56])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 0.21/0.57    inference(equality_resolution,[],[f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.57  fof(f97,plain,(
% 0.21/0.57    ( ! [X4,X5] : (r2_hidden(X5,k4_xboole_0(k4_xboole_0(X4,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK1))) | r2_hidden(X5,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))) | ~r2_hidden(X5,X4)) ) | ~spl5_4),
% 0.21/0.57    inference(superposition,[],[f55,f87])).
% 0.21/0.57  fof(f87,plain,(
% 0.21/0.57    ( ! [X0] : (k4_xboole_0(k4_xboole_0(X0,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK1)) = k4_xboole_0(X0,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))) ) | ~spl5_4),
% 0.21/0.57    inference(superposition,[],[f50,f85])).
% 0.21/0.57  fof(f85,plain,(
% 0.21/0.57    k3_tarski(k1_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))) = k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))) | ~spl5_4),
% 0.21/0.57    inference(avatar_component_clause,[],[f83])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2)))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f31,f46])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 0.21/0.57    inference(equality_resolution,[],[f37])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f1])).
% 0.21/0.57  fof(f284,plain,(
% 0.21/0.57    ~r1_tarski(sK1,k3_tarski(k1_enumset1(sK0,sK0,sK1))) | spl5_18),
% 0.21/0.57    inference(avatar_component_clause,[],[f282])).
% 0.21/0.57  fof(f285,plain,(
% 0.21/0.57    spl5_17 | ~spl5_18 | ~spl5_14),
% 0.21/0.57    inference(avatar_split_clause,[],[f268,f210,f282,f278])).
% 0.21/0.57  fof(f278,plain,(
% 0.21/0.57    spl5_17 <=> sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.57  fof(f210,plain,(
% 0.21/0.57    spl5_14 <=> r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.57  fof(f268,plain,(
% 0.21/0.57    ~r1_tarski(sK1,k3_tarski(k1_enumset1(sK0,sK0,sK1))) | sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~spl5_14),
% 0.21/0.57    inference(resolution,[],[f212,f23])).
% 0.21/0.57  fof(f212,plain,(
% 0.21/0.57    r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK1) | ~spl5_14),
% 0.21/0.57    inference(avatar_component_clause,[],[f210])).
% 0.21/0.57  fof(f267,plain,(
% 0.21/0.57    ~spl5_15),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f244])).
% 0.21/0.57  fof(f244,plain,(
% 0.21/0.57    $false | ~spl5_15),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f59,f227,f227,f55])).
% 0.21/0.57  fof(f227,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),X0)) ) | ~spl5_15),
% 0.21/0.57    inference(avatar_component_clause,[],[f226])).
% 0.21/0.57  fof(f226,plain,(
% 0.21/0.57    spl5_15 <=> ! [X0] : ~r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),X0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.57  fof(f59,plain,(
% 0.21/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_enumset1(X0,X1,X4))) )),
% 0.21/0.57    inference(equality_resolution,[],[f58])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k1_enumset1(X0,X1,X4) != X3) )),
% 0.21/0.57    inference(equality_resolution,[],[f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.57    inference(cnf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.57  fof(f232,plain,(
% 0.21/0.57    spl5_15 | spl5_16 | ~spl5_13),
% 0.21/0.57    inference(avatar_split_clause,[],[f224,f205,f229,f226])).
% 0.21/0.57  fof(f205,plain,(
% 0.21/0.57    spl5_13 <=> ! [X1] : ~r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k4_xboole_0(X1,k1_zfmisc_1(sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.57  fof(f224,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK0)) | ~r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),X0)) ) | ~spl5_13),
% 0.21/0.57    inference(resolution,[],[f206,f55])).
% 0.21/0.57  fof(f206,plain,(
% 0.21/0.57    ( ! [X1] : (~r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k4_xboole_0(X1,k1_zfmisc_1(sK0)))) ) | ~spl5_13),
% 0.21/0.57    inference(avatar_component_clause,[],[f205])).
% 0.21/0.57  fof(f213,plain,(
% 0.21/0.57    spl5_14 | ~spl5_12),
% 0.21/0.57    inference(avatar_split_clause,[],[f208,f201,f210])).
% 0.21/0.57  fof(f201,plain,(
% 0.21/0.57    spl5_12 <=> r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.57  fof(f208,plain,(
% 0.21/0.57    r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK1) | ~spl5_12),
% 0.21/0.57    inference(resolution,[],[f203,f53])).
% 0.21/0.57  fof(f203,plain,(
% 0.21/0.57    r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK1)) | ~spl5_12),
% 0.21/0.57    inference(avatar_component_clause,[],[f201])).
% 0.21/0.57  fof(f207,plain,(
% 0.21/0.57    spl5_12 | spl5_13 | ~spl5_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f124,f83,f205,f201])).
% 0.21/0.57  fof(f124,plain,(
% 0.21/0.57    ( ! [X1] : (~r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k4_xboole_0(X1,k1_zfmisc_1(sK0))) | r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK1))) ) | ~spl5_4),
% 0.21/0.57    inference(resolution,[],[f117,f52])).
% 0.21/0.57  fof(f117,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k3_tarski(k1_enumset1(sK0,sK0,sK1))) | ~r2_hidden(X0,k4_xboole_0(X1,k1_zfmisc_1(sK0))) | r2_hidden(X0,k1_zfmisc_1(sK1))) ) | ~spl5_4),
% 0.21/0.57    inference(resolution,[],[f103,f54])).
% 0.21/0.57  fof(f103,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))) | r2_hidden(X0,k1_zfmisc_1(sK1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_zfmisc_1(sK0)))) ) | ~spl5_4),
% 0.21/0.57    inference(resolution,[],[f96,f55])).
% 0.21/0.57  fof(f96,plain,(
% 0.21/0.57    ( ! [X2,X3] : (~r2_hidden(X3,k4_xboole_0(k4_xboole_0(X2,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK1))) | ~r2_hidden(X3,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))) ) | ~spl5_4),
% 0.21/0.57    inference(superposition,[],[f56,f87])).
% 0.21/0.57  fof(f86,plain,(
% 0.21/0.57    spl5_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f47,f83])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    k3_tarski(k1_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))) = k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))),
% 0.21/0.57    inference(definition_unfolding,[],[f15,f46,f46])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1))),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    ? [X0,X1] : (~r3_xboole_0(X0,X1) & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1] : (k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) => r3_xboole_0(X0,X1))),
% 0.21/0.57    inference(negated_conjecture,[],[f11])).
% 0.21/0.57  fof(f11,conjecture,(
% 0.21/0.57    ! [X0,X1] : (k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) => r3_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_zfmisc_1)).
% 0.21/0.57  fof(f81,plain,(
% 0.21/0.57    ~spl5_3 | spl5_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f71,f66,f78])).
% 0.21/0.57  fof(f78,plain,(
% 0.21/0.57    spl5_3 <=> r1_tarski(sK1,sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.57  fof(f66,plain,(
% 0.21/0.57    spl5_1 <=> r3_xboole_0(sK0,sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.57  fof(f71,plain,(
% 0.21/0.57    ~r1_tarski(sK1,sK0) | spl5_1),
% 0.21/0.57    inference(resolution,[],[f68,f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r3_xboole_0(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : (r3_xboole_0(X0,X1) <=> (r1_tarski(X1,X0) | r1_tarski(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).
% 0.21/0.57  fof(f68,plain,(
% 0.21/0.57    ~r3_xboole_0(sK0,sK1) | spl5_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f66])).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    ~spl5_2 | spl5_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f70,f66,f73])).
% 0.21/0.57  fof(f73,plain,(
% 0.21/0.57    spl5_2 <=> r1_tarski(sK0,sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.57  fof(f70,plain,(
% 0.21/0.57    ~r1_tarski(sK0,sK1) | spl5_1),
% 0.21/0.57    inference(resolution,[],[f68,f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r3_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f3])).
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    ~spl5_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f16,f66])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ~r3_xboole_0(sK0,sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (18413)------------------------------
% 0.21/0.57  % (18413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (18413)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (18413)Memory used [KB]: 10874
% 0.21/0.57  % (18413)Time elapsed: 0.147 s
% 0.21/0.57  % (18413)------------------------------
% 0.21/0.57  % (18413)------------------------------
% 0.21/0.57  % (18383)Success in time 0.209 s
%------------------------------------------------------------------------------
