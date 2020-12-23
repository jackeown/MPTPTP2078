%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0898+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:56 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   41 (  63 expanded)
%              Number of leaves         :    9 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  131 ( 199 expanded)
%              Number of equality atoms :   92 ( 147 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1456,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1396,f1400,f1419,f1432,f1446,f1455])).

fof(f1455,plain,
    ( ~ spl2_4
    | spl2_6 ),
    inference(avatar_contradiction_clause,[],[f1454])).

fof(f1454,plain,
    ( $false
    | ~ spl2_4
    | spl2_6 ),
    inference(subsumption_resolution,[],[f1452,f1445])).

fof(f1445,plain,
    ( k1_xboole_0 != sK0
    | spl2_6 ),
    inference(avatar_component_clause,[],[f1444])).

fof(f1444,plain,
    ( spl2_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f1452,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_4 ),
    inference(trivial_inequality_removal,[],[f1451])).

fof(f1451,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | ~ spl2_4 ),
    inference(duplicate_literal_removal,[],[f1450])).

fof(f1450,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | ~ spl2_4 ),
    inference(superposition,[],[f1381,f1434])).

fof(f1434,plain,
    ( k1_xboole_0 = k4_zfmisc_1(sK0,sK0,sK0,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f1417])).

fof(f1417,plain,
    ( spl2_4
  <=> k1_xboole_0 = k4_zfmisc_1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f1381,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1370])).

fof(f1370,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f1369])).

fof(f1369,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f1352])).

fof(f1352,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f1446,plain,
    ( ~ spl2_6
    | spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f1440,f1414,f1394,f1444])).

fof(f1394,plain,
    ( spl2_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1414,plain,
    ( spl2_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f1440,plain,
    ( k1_xboole_0 != sK0
    | spl2_1
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f1395,f1415])).

fof(f1415,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f1414])).

fof(f1395,plain,
    ( sK0 != sK1
    | spl2_1 ),
    inference(avatar_component_clause,[],[f1394])).

fof(f1432,plain,
    ( spl2_1
    | ~ spl2_2
    | spl2_4 ),
    inference(avatar_contradiction_clause,[],[f1420])).

fof(f1420,plain,
    ( $false
    | spl2_1
    | ~ spl2_2
    | spl2_4 ),
    inference(unit_resulting_resolution,[],[f1395,f1418,f1399,f1373])).

fof(f1373,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7)
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f1364])).

fof(f1364,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f1363])).

fof(f1363,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f1354])).

fof(f1354,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_mcart_1)).

fof(f1399,plain,
    ( k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f1398])).

fof(f1398,plain,
    ( spl2_2
  <=> k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1418,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK0,sK0,sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f1417])).

fof(f1419,plain,
    ( spl2_3
    | ~ spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f1412,f1398,f1417,f1414])).

fof(f1412,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK1
    | ~ spl2_2 ),
    inference(duplicate_literal_removal,[],[f1407])).

fof(f1407,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | ~ spl2_2 ),
    inference(superposition,[],[f1381,f1399])).

fof(f1400,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f1371,f1398])).

fof(f1371,plain,(
    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f1368])).

fof(f1368,plain,
    ( sK0 != sK1
    & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1362,f1367])).

fof(f1367,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) )
   => ( sK0 != sK1
      & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1362,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) ) ),
    inference(ennf_transformation,[],[f1356])).

fof(f1356,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f1355])).

fof(f1355,conjecture,(
    ! [X0,X1] :
      ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_mcart_1)).

fof(f1396,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f1372,f1394])).

fof(f1372,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f1368])).
%------------------------------------------------------------------------------
