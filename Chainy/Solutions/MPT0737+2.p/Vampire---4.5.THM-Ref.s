%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0737+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 (  94 expanded)
%              Number of leaves         :   13 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :  144 ( 273 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1337,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1159,f1164,f1169,f1246,f1252,f1296,f1304,f1336])).

fof(f1336,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | spl4_24
    | spl4_23 ),
    inference(avatar_split_clause,[],[f1333,f1293,f1301,f1166,f1161])).

fof(f1161,plain,
    ( spl4_5
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f1166,plain,
    ( spl4_6
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f1301,plain,
    ( spl4_24
  <=> r1_ordinal1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f1293,plain,
    ( spl4_23
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f1333,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | spl4_23 ),
    inference(resolution,[],[f1295,f1131])).

fof(f1131,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f1091])).

fof(f1091,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f1090])).

fof(f1090,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1056])).

fof(f1056,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f1295,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | spl4_23 ),
    inference(avatar_component_clause,[],[f1293])).

fof(f1304,plain,
    ( ~ spl4_24
    | ~ spl4_5
    | ~ spl4_6
    | spl4_20 ),
    inference(avatar_split_clause,[],[f1297,f1249,f1166,f1161,f1301])).

fof(f1249,plain,
    ( spl4_20
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f1297,plain,
    ( ~ r1_ordinal1(sK1,sK0)
    | ~ spl4_5
    | ~ spl4_6
    | spl4_20 ),
    inference(unit_resulting_resolution,[],[f1163,f1168,f1251,f1129])).

fof(f1129,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f1114])).

fof(f1114,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f1089])).

fof(f1089,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f1088])).

fof(f1088,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1065])).

fof(f1065,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f1251,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl4_20 ),
    inference(avatar_component_clause,[],[f1249])).

fof(f1168,plain,
    ( v3_ordinal1(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f1166])).

fof(f1163,plain,
    ( v3_ordinal1(sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f1161])).

fof(f1296,plain,
    ( ~ spl4_23
    | ~ spl4_5
    | ~ spl4_6
    | spl4_19 ),
    inference(avatar_split_clause,[],[f1291,f1243,f1166,f1161,f1293])).

fof(f1243,plain,
    ( spl4_19
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f1291,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ spl4_5
    | ~ spl4_6
    | spl4_19 ),
    inference(unit_resulting_resolution,[],[f1168,f1163,f1245,f1129])).

fof(f1245,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl4_19 ),
    inference(avatar_component_clause,[],[f1243])).

fof(f1252,plain,
    ( ~ spl4_20
    | spl4_4 ),
    inference(avatar_split_clause,[],[f1247,f1156,f1249])).

% (23160)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=2.0:amm=sco:anc=none:gs=on:gsem=off:lma=on:lwlo=on:nm=4:nwc=10:stl=30:sd=3:ss=axioms:sos=all:sac=on_49 on theBenchmark
fof(f1156,plain,
    ( spl4_4
  <=> r3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f1247,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f1158,f1124])).

fof(f1124,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1111])).

fof(f1111,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f1110])).

fof(f1110,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).

fof(f1158,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f1156])).

fof(f1246,plain,
    ( ~ spl4_19
    | spl4_4 ),
    inference(avatar_split_clause,[],[f1241,f1156,f1243])).

fof(f1241,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f1158,f1123])).

fof(f1123,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1111])).

fof(f1169,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f1115,f1166])).

fof(f1115,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f1107])).

fof(f1107,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1084,f1106,f1105])).

fof(f1105,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r3_xboole_0(X0,X1)
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ~ r3_xboole_0(sK0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1106,plain,
    ( ? [X1] :
        ( ~ r3_xboole_0(sK0,X1)
        & v3_ordinal1(X1) )
   => ( ~ r3_xboole_0(sK0,sK1)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1084,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1077])).

fof(f1077,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => r3_xboole_0(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f1076])).

fof(f1076,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => r3_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_ordinal1)).

fof(f1164,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f1116,f1161])).

fof(f1116,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f1107])).

fof(f1159,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f1117,f1156])).

fof(f1117,plain,(
    ~ r3_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f1107])).
%------------------------------------------------------------------------------
