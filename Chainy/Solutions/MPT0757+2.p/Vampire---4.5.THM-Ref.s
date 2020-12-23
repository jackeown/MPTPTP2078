%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0757+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:47 EST 2020

% Result     : Theorem 1.85s
% Output     : Refutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 123 expanded)
%              Number of leaves         :   15 (  54 expanded)
%              Depth                    :    7
%              Number of atoms          :  180 ( 448 expanded)
%              Number of equality atoms :   18 (  65 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2403,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1514,f1519,f1524,f1529,f1534,f1931,f1936,f2119,f2338,f2402])).

fof(f2402,plain,
    ( ~ spl37_8
    | ~ spl37_7
    | spl37_105
    | spl37_76 ),
    inference(avatar_split_clause,[],[f2392,f2116,f2335,f1526,f1531])).

fof(f1531,plain,
    ( spl37_8
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_8])])).

fof(f1526,plain,
    ( spl37_7
  <=> v3_ordinal1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_7])])).

fof(f2335,plain,
    ( spl37_105
  <=> r1_ordinal1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_105])])).

fof(f2116,plain,
    ( spl37_76
  <=> r1_ordinal1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_76])])).

fof(f2392,plain,
    ( r1_ordinal1(sK1,sK2)
    | ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK1)
    | spl37_76 ),
    inference(resolution,[],[f2118,f1417])).

fof(f1417,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f1184])).

fof(f1184,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f1183])).

fof(f1183,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1058])).

fof(f1058,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f2118,plain,
    ( ~ r1_ordinal1(sK2,sK1)
    | spl37_76 ),
    inference(avatar_component_clause,[],[f2116])).

fof(f2338,plain,
    ( ~ spl37_105
    | ~ spl37_7
    | ~ spl37_8
    | spl37_50 ),
    inference(avatar_split_clause,[],[f2325,f1933,f1531,f1526,f2335])).

fof(f1933,plain,
    ( spl37_50
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_50])])).

fof(f2325,plain,
    ( ~ r1_ordinal1(sK1,sK2)
    | ~ spl37_7
    | ~ spl37_8
    | spl37_50 ),
    inference(unit_resulting_resolution,[],[f1533,f1528,f1935,f1415])).

fof(f1415,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f1271])).

fof(f1271,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f1182])).

fof(f1182,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f1181])).

fof(f1181,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1080])).

fof(f1080,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f1935,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl37_50 ),
    inference(avatar_component_clause,[],[f1933])).

fof(f1528,plain,
    ( v3_ordinal1(sK2)
    | ~ spl37_7 ),
    inference(avatar_component_clause,[],[f1526])).

fof(f1533,plain,
    ( v3_ordinal1(sK1)
    | ~ spl37_8 ),
    inference(avatar_component_clause,[],[f1531])).

fof(f2119,plain,
    ( ~ spl37_76
    | ~ spl37_7
    | ~ spl37_8
    | spl37_49 ),
    inference(avatar_split_clause,[],[f2106,f1928,f1531,f1526,f2116])).

fof(f1928,plain,
    ( spl37_49
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_49])])).

fof(f2106,plain,
    ( ~ r1_ordinal1(sK2,sK1)
    | ~ spl37_7
    | ~ spl37_8
    | spl37_49 ),
    inference(unit_resulting_resolution,[],[f1528,f1533,f1930,f1415])).

fof(f1930,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl37_49 ),
    inference(avatar_component_clause,[],[f1928])).

fof(f1936,plain,
    ( ~ spl37_50
    | spl37_5
    | spl37_6 ),
    inference(avatar_split_clause,[],[f1915,f1521,f1516,f1933])).

fof(f1516,plain,
    ( spl37_5
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_5])])).

fof(f1521,plain,
    ( spl37_6
  <=> r2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_6])])).

fof(f1915,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl37_5
    | spl37_6 ),
    inference(unit_resulting_resolution,[],[f1523,f1518,f1401])).

fof(f1401,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1268])).

fof(f1268,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f1267])).

fof(f1267,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f1518,plain,
    ( sK1 != sK2
    | spl37_5 ),
    inference(avatar_component_clause,[],[f1516])).

fof(f1523,plain,
    ( ~ r2_xboole_0(sK1,sK2)
    | spl37_6 ),
    inference(avatar_component_clause,[],[f1521])).

fof(f1931,plain,
    ( ~ spl37_49
    | spl37_4
    | spl37_5 ),
    inference(avatar_split_clause,[],[f1916,f1516,f1511,f1928])).

fof(f1511,plain,
    ( spl37_4
  <=> r2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl37_4])])).

fof(f1916,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl37_4
    | spl37_5 ),
    inference(unit_resulting_resolution,[],[f1513,f1518,f1401])).

fof(f1513,plain,
    ( ~ r2_xboole_0(sK2,sK1)
    | spl37_4 ),
    inference(avatar_component_clause,[],[f1511])).

fof(f1534,plain,(
    spl37_8 ),
    inference(avatar_split_clause,[],[f1306,f1531])).

fof(f1306,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f1219])).

fof(f1219,plain,
    ( ~ r2_xboole_0(sK2,sK1)
    & sK1 != sK2
    & ~ r2_xboole_0(sK1,sK2)
    & v3_ordinal1(sK2)
    & v3_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f1131,f1218,f1217])).

fof(f1217,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_xboole_0(X1,X0)
            & X0 != X1
            & ~ r2_xboole_0(X0,X1)
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ~ r2_xboole_0(X1,sK1)
          & sK1 != X1
          & ~ r2_xboole_0(sK1,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1218,plain,
    ( ? [X1] :
        ( ~ r2_xboole_0(X1,sK1)
        & sK1 != X1
        & ~ r2_xboole_0(sK1,X1)
        & v3_ordinal1(X1) )
   => ( ~ r2_xboole_0(sK2,sK1)
      & sK1 != sK2
      & ~ r2_xboole_0(sK1,sK2)
      & v3_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f1131,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f1130])).

fof(f1130,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1118])).

fof(f1118,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ~ ( ~ r2_xboole_0(X1,X0)
                & X0 != X1
                & ~ r2_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f1117])).

fof(f1117,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_xboole_0(X1,X0)
              & X0 != X1
              & ~ r2_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_ordinal1)).

fof(f1529,plain,(
    spl37_7 ),
    inference(avatar_split_clause,[],[f1307,f1526])).

fof(f1307,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f1219])).

fof(f1524,plain,(
    ~ spl37_6 ),
    inference(avatar_split_clause,[],[f1308,f1521])).

fof(f1308,plain,(
    ~ r2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f1219])).

fof(f1519,plain,(
    ~ spl37_5 ),
    inference(avatar_split_clause,[],[f1309,f1516])).

fof(f1309,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f1219])).

fof(f1514,plain,(
    ~ spl37_4 ),
    inference(avatar_split_clause,[],[f1310,f1511])).

fof(f1310,plain,(
    ~ r2_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f1219])).
%------------------------------------------------------------------------------
