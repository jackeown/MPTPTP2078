%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0878+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 105 expanded)
%              Number of leaves         :    8 (  33 expanded)
%              Depth                    :   13
%              Number of atoms          :  121 ( 255 expanded)
%              Number of equality atoms :   98 ( 227 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1970,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1436,f1496,f1532,f1969])).

fof(f1969,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f1968])).

fof(f1968,plain,
    ( $false
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f1964,f1349])).

fof(f1349,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f1340])).

fof(f1340,plain,
    ( sK0 != sK1
    & k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1333,f1339])).

% (21862)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_6 on theBenchmark
fof(f1339,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) )
   => ( sK0 != sK1
      & k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1333,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) ) ),
    inference(ennf_transformation,[],[f1325])).

fof(f1325,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f1324])).

fof(f1324,conjecture,(
    ! [X0,X1] :
      ( k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_mcart_1)).

fof(f1964,plain,
    ( sK0 = sK1
    | ~ spl3_2 ),
    inference(equality_resolution,[],[f1419])).

fof(f1419,plain,
    ( ! [X2,X0,X1] :
        ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)
        | sK1 = X2 )
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f1418])).

fof(f1418,plain,
    ( spl3_2
  <=> ! [X1,X0,X2] :
        ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)
        | sK1 = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1532,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f1501,f1418,f1414])).

fof(f1414,plain,
    ( spl3_1
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1501,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)
      | sK1 = X2 ) ),
    inference(superposition,[],[f1367,f1366])).

fof(f1366,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) ),
    inference(definition_unfolding,[],[f1348,f1365,f1365])).

fof(f1365,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1275])).

fof(f1275,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f1348,plain,(
    k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f1340])).

% (21858)Refutation not found, incomplete strategy% (21858)------------------------------
% (21858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21858)Termination reason: Refutation not found, incomplete strategy

% (21858)Memory used [KB]: 7164
% (21858)Time elapsed: 0.003 s
% (21858)------------------------------
% (21858)------------------------------
fof(f1367,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | X2 = X5 ) ),
    inference(definition_unfolding,[],[f1357,f1365,f1365,f1365])).

fof(f1357,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f1336])).

% (21867)dis+10_5:4_add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence:urr=on:updr=off_15 on theBenchmark
fof(f1336,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f1335])).

fof(f1335,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f1323])).

fof(f1323,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_mcart_1)).

fof(f1496,plain,(
    ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f1495])).

fof(f1495,plain,
    ( $false
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f1488,f1458])).

fof(f1458,plain,
    ( k1_xboole_0 != sK0
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f1349,f1432])).

fof(f1432,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f1430])).

fof(f1430,plain,
    ( spl3_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f1488,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_5 ),
    inference(trivial_inequality_removal,[],[f1487])).

fof(f1487,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | ~ spl3_5 ),
    inference(duplicate_literal_removal,[],[f1472])).

fof(f1472,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | ~ spl3_5 ),
    inference(superposition,[],[f1376,f1459])).

fof(f1459,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f1457,f1379])).

fof(f1379,plain,(
    ! [X0,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0) ),
    inference(equality_resolution,[],[f1373])).

fof(f1373,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f1364,f1365])).

fof(f1364,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f1347])).

fof(f1347,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f1346])).

fof(f1346,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f1321])).

fof(f1321,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f1457,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f1366,f1432])).

fof(f1376,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f1361,f1365])).

fof(f1361,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1347])).

fof(f1436,plain,
    ( spl3_5
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f1409,f1414,f1430])).

fof(f1409,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f1394])).

fof(f1394,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f1376,f1366])).
%------------------------------------------------------------------------------
