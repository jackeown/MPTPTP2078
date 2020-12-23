%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:15 EST 2020

% Result     : Theorem 3.56s
% Output     : Refutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 165 expanded)
%              Number of leaves         :   27 (  72 expanded)
%              Depth                    :   10
%              Number of atoms          :  445 ( 720 expanded)
%              Number of equality atoms :  151 ( 206 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2151,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f108,f112,f140,f148,f190,f375,f379,f400,f490,f527,f909,f982,f1101,f1432,f2116,f2149])).

fof(f2149,plain,
    ( spl6_2
    | ~ spl6_12
    | ~ spl6_40
    | spl6_96
    | ~ spl6_120 ),
    inference(avatar_contradiction_clause,[],[f2148])).

fof(f2148,plain,
    ( $false
    | spl6_2
    | ~ spl6_12
    | ~ spl6_40
    | spl6_96
    | ~ spl6_120 ),
    inference(subsumption_resolution,[],[f1431,f2147])).

fof(f2147,plain,
    ( r2_hidden(sK0,sK1)
    | spl6_2
    | ~ spl6_12
    | ~ spl6_40
    | ~ spl6_120 ),
    inference(forward_demodulation,[],[f2118,f2119])).

fof(f2119,plain,
    ( sK0 = sK4(k1_tarski(sK0),sK1,k1_tarski(sK0))
    | ~ spl6_12
    | ~ spl6_120 ),
    inference(unit_resulting_resolution,[],[f2115,f147])).

fof(f147,plain,
    ( ! [X0,X3] :
        ( ~ r2_hidden(X3,k1_tarski(X0))
        | X0 = X3 )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl6_12
  <=> ! [X3,X0] :
        ( X0 = X3
        | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f2115,plain,
    ( r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl6_120 ),
    inference(avatar_component_clause,[],[f2113])).

fof(f2113,plain,
    ( spl6_120
  <=> r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_120])])).

fof(f2118,plain,
    ( r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),sK1)
    | spl6_2
    | ~ spl6_40
    | ~ spl6_120 ),
    inference(unit_resulting_resolution,[],[f107,f2115,f2115,f399])).

fof(f399,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK4(X0,X1,X2),X2)
        | r2_hidden(sK4(X0,X1,X2),X1)
        | ~ r2_hidden(sK4(X0,X1,X2),X0)
        | k4_xboole_0(X0,X1) = X2 )
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f398])).

fof(f398,plain,
    ( spl6_40
  <=> ! [X1,X0,X2] :
        ( k4_xboole_0(X0,X1) = X2
        | r2_hidden(sK4(X0,X1,X2),X1)
        | ~ r2_hidden(sK4(X0,X1,X2),X0)
        | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f107,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl6_2
  <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1431,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl6_96 ),
    inference(avatar_component_clause,[],[f1429])).

fof(f1429,plain,
    ( spl6_96
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_96])])).

fof(f2116,plain,
    ( spl6_120
    | spl6_2
    | ~ spl6_84 ),
    inference(avatar_split_clause,[],[f983,f980,f105,f2113])).

fof(f980,plain,
    ( spl6_84
  <=> ! [X1,X0] :
        ( r2_hidden(sK4(X0,X1,X0),X0)
        | k4_xboole_0(X0,X1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).

fof(f983,plain,
    ( r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | spl6_2
    | ~ spl6_84 ),
    inference(unit_resulting_resolution,[],[f107,f981])).

fof(f981,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1,X0),X0)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl6_84 ),
    inference(avatar_component_clause,[],[f980])).

fof(f1432,plain,
    ( ~ spl6_96
    | spl6_51
    | ~ spl6_87 ),
    inference(avatar_split_clause,[],[f1315,f1098,f524,f1429])).

fof(f524,plain,
    ( spl6_51
  <=> r2_hidden(sK4(k1_tarski(sK0),sK1,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f1098,plain,
    ( spl6_87
  <=> sK0 = sK4(k1_tarski(sK0),sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).

fof(f1315,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl6_51
    | ~ spl6_87 ),
    inference(superposition,[],[f526,f1100])).

fof(f1100,plain,
    ( sK0 = sK4(k1_tarski(sK0),sK1,k1_xboole_0)
    | ~ spl6_87 ),
    inference(avatar_component_clause,[],[f1098])).

fof(f526,plain,
    ( ~ r2_hidden(sK4(k1_tarski(sK0),sK1,k1_xboole_0),sK1)
    | spl6_51 ),
    inference(avatar_component_clause,[],[f524])).

fof(f1101,plain,
    ( spl6_87
    | ~ spl6_12
    | ~ spl6_78 ),
    inference(avatar_split_clause,[],[f943,f906,f146,f1098])).

fof(f906,plain,
    ( spl6_78
  <=> r2_hidden(sK4(k1_tarski(sK0),sK1,k1_xboole_0),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f943,plain,
    ( sK0 = sK4(k1_tarski(sK0),sK1,k1_xboole_0)
    | ~ spl6_12
    | ~ spl6_78 ),
    inference(unit_resulting_resolution,[],[f908,f147])).

fof(f908,plain,
    ( r2_hidden(sK4(k1_tarski(sK0),sK1,k1_xboole_0),k1_tarski(sK0))
    | ~ spl6_78 ),
    inference(avatar_component_clause,[],[f906])).

fof(f982,plain,
    ( spl6_84
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f393,f373,f980])).

fof(f373,plain,
    ( spl6_36
  <=> ! [X1,X0,X2] :
        ( k4_xboole_0(X0,X1) = X2
        | r2_hidden(sK4(X0,X1,X2),X0)
        | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f393,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1,X0),X0)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl6_36 ),
    inference(factoring,[],[f374])).

fof(f374,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK4(X0,X1,X2),X2)
        | r2_hidden(sK4(X0,X1,X2),X0)
        | k4_xboole_0(X0,X1) = X2 )
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f373])).

fof(f909,plain,
    ( spl6_78
    | spl6_1
    | ~ spl6_36
    | ~ spl6_49 ),
    inference(avatar_split_clause,[],[f499,f488,f373,f100,f906])).

fof(f100,plain,
    ( spl6_1
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f488,plain,
    ( spl6_49
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f499,plain,
    ( r2_hidden(sK4(k1_tarski(sK0),sK1,k1_xboole_0),k1_tarski(sK0))
    | spl6_1
    | ~ spl6_36
    | ~ spl6_49 ),
    inference(unit_resulting_resolution,[],[f102,f489,f374])).

fof(f489,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f488])).

fof(f102,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f527,plain,
    ( ~ spl6_51
    | spl6_1
    | ~ spl6_37
    | ~ spl6_49 ),
    inference(avatar_split_clause,[],[f498,f488,f377,f100,f524])).

fof(f377,plain,
    ( spl6_37
  <=> ! [X1,X0,X2] :
        ( k4_xboole_0(X0,X1) = X2
        | ~ r2_hidden(sK4(X0,X1,X2),X1)
        | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f498,plain,
    ( ~ r2_hidden(sK4(k1_tarski(sK0),sK1,k1_xboole_0),sK1)
    | spl6_1
    | ~ spl6_37
    | ~ spl6_49 ),
    inference(unit_resulting_resolution,[],[f102,f489,f378])).

fof(f378,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK4(X0,X1,X2),X1)
        | k4_xboole_0(X0,X1) = X2
        | r2_hidden(sK4(X0,X1,X2),X2) )
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f377])).

fof(f490,plain,
    ( spl6_49
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f233,f188,f138,f110,f488])).

fof(f110,plain,
    ( spl6_3
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f138,plain,
    ( spl6_10
  <=> ! [X1,X5,X2] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f188,plain,
    ( spl6_20
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f233,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_20 ),
    inference(unit_resulting_resolution,[],[f139,f111,f189])).

fof(f189,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) )
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f188])).

fof(f111,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f139,plain,
    ( ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f138])).

fof(f400,plain,(
    spl6_40 ),
    inference(avatar_split_clause,[],[f69,f398])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f379,plain,(
    spl6_37 ),
    inference(avatar_split_clause,[],[f68,f377])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f375,plain,(
    spl6_36 ),
    inference(avatar_split_clause,[],[f67,f373])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f190,plain,(
    spl6_20 ),
    inference(avatar_split_clause,[],[f57,f188])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f148,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f84,f146])).

fof(f84,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f140,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f93,f138])).

fof(f93,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK5(X0,X1,X2,X3) != X2
              & sK5(X0,X1,X2,X3) != X1
              & sK5(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
          & ( sK5(X0,X1,X2,X3) = X2
            | sK5(X0,X1,X2,X3) = X1
            | sK5(X0,X1,X2,X3) = X0
            | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).

fof(f42,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK5(X0,X1,X2,X3) != X2
            & sK5(X0,X1,X2,X3) != X1
            & sK5(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
        & ( sK5(X0,X1,X2,X3) = X2
          | sK5(X0,X1,X2,X3) = X1
          | sK5(X0,X1,X2,X3) = X0
          | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f112,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f46,f110])).

fof(f46,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f108,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f45,f105])).

fof(f45,plain,(
    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
        & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

fof(f103,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f44,f100])).

fof(f44,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:05:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (2600)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (2624)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (2614)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (2614)Refutation not found, incomplete strategy% (2614)------------------------------
% 0.21/0.53  % (2614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2614)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (2614)Memory used [KB]: 1663
% 0.21/0.53  % (2614)Time elapsed: 0.116 s
% 0.21/0.53  % (2614)------------------------------
% 0.21/0.53  % (2614)------------------------------
% 0.21/0.53  % (2602)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (2613)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (2624)Refutation not found, incomplete strategy% (2624)------------------------------
% 0.21/0.53  % (2624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2624)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (2624)Memory used [KB]: 10746
% 0.21/0.53  % (2624)Time elapsed: 0.115 s
% 0.21/0.53  % (2624)------------------------------
% 0.21/0.53  % (2624)------------------------------
% 0.21/0.53  % (2629)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (2601)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (2627)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (2629)Refutation not found, incomplete strategy% (2629)------------------------------
% 0.21/0.54  % (2629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2629)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (2629)Memory used [KB]: 1663
% 0.21/0.54  % (2629)Time elapsed: 0.064 s
% 0.21/0.54  % (2629)------------------------------
% 0.21/0.54  % (2629)------------------------------
% 0.21/0.54  % (2601)Refutation not found, incomplete strategy% (2601)------------------------------
% 0.21/0.54  % (2601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2601)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (2601)Memory used [KB]: 1663
% 0.21/0.54  % (2601)Time elapsed: 0.122 s
% 0.21/0.54  % (2601)------------------------------
% 0.21/0.54  % (2601)------------------------------
% 0.21/0.54  % (2610)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (2618)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (2608)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (2618)Refutation not found, incomplete strategy% (2618)------------------------------
% 0.21/0.54  % (2618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2618)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (2618)Memory used [KB]: 1663
% 0.21/0.54  % (2618)Time elapsed: 0.127 s
% 0.21/0.54  % (2618)------------------------------
% 0.21/0.54  % (2618)------------------------------
% 0.21/0.54  % (2605)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (2626)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (2620)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (2604)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.49/0.55  % (2623)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.49/0.55  % (2626)Refutation not found, incomplete strategy% (2626)------------------------------
% 1.49/0.55  % (2626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (2626)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.55  
% 1.49/0.55  % (2626)Memory used [KB]: 6268
% 1.49/0.55  % (2626)Time elapsed: 0.127 s
% 1.49/0.55  % (2626)------------------------------
% 1.49/0.55  % (2626)------------------------------
% 1.49/0.55  % (2606)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.49/0.55  % (2615)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.49/0.55  % (2616)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.49/0.55  % (2616)Refutation not found, incomplete strategy% (2616)------------------------------
% 1.49/0.55  % (2616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (2616)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.55  
% 1.49/0.55  % (2616)Memory used [KB]: 10618
% 1.49/0.55  % (2616)Time elapsed: 0.147 s
% 1.49/0.55  % (2616)------------------------------
% 1.49/0.55  % (2616)------------------------------
% 1.49/0.55  % (2621)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.49/0.56  % (2612)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.49/0.56  % (2627)Refutation not found, incomplete strategy% (2627)------------------------------
% 1.49/0.56  % (2627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (2627)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (2627)Memory used [KB]: 6268
% 1.49/0.56  % (2627)Time elapsed: 0.151 s
% 1.49/0.56  % (2627)------------------------------
% 1.49/0.56  % (2627)------------------------------
% 1.49/0.57  % (2628)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.58/0.57  % (2609)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.58/0.57  % (2607)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.58/0.57  % (2625)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.58/0.57  % (2619)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.58/0.57  % (2603)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.58/0.58  % (2611)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.58/0.58  % (2617)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.58/0.59  % (2617)Refutation not found, incomplete strategy% (2617)------------------------------
% 1.58/0.59  % (2617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.59  % (2617)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.59  
% 1.58/0.59  % (2617)Memory used [KB]: 1791
% 1.58/0.59  % (2617)Time elapsed: 0.178 s
% 1.58/0.59  % (2617)------------------------------
% 1.58/0.59  % (2617)------------------------------
% 1.58/0.59  % (2622)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 2.16/0.66  % (2631)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.16/0.66  % (2632)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.16/0.67  % (2635)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.16/0.67  % (2634)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.16/0.67  % (2635)Refutation not found, incomplete strategy% (2635)------------------------------
% 2.16/0.67  % (2635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.67  % (2635)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.67  
% 2.16/0.67  % (2635)Memory used [KB]: 10746
% 2.16/0.67  % (2635)Time elapsed: 0.109 s
% 2.16/0.67  % (2635)------------------------------
% 2.16/0.67  % (2635)------------------------------
% 2.16/0.68  % (2630)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.16/0.70  % (2637)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.16/0.71  % (2638)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.16/0.72  % (2636)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.70/0.74  % (2603)Refutation not found, incomplete strategy% (2603)------------------------------
% 2.70/0.74  % (2603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.70/0.74  % (2603)Termination reason: Refutation not found, incomplete strategy
% 2.70/0.74  
% 2.70/0.74  % (2603)Memory used [KB]: 6140
% 2.70/0.74  % (2603)Time elapsed: 0.308 s
% 2.70/0.74  % (2603)------------------------------
% 2.70/0.74  % (2603)------------------------------
% 2.93/0.78  % (2639)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.93/0.82  % (2602)Time limit reached!
% 2.93/0.82  % (2602)------------------------------
% 2.93/0.82  % (2602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.93/0.82  % (2602)Termination reason: Time limit
% 2.93/0.82  
% 2.93/0.82  % (2602)Memory used [KB]: 6268
% 2.93/0.82  % (2602)Time elapsed: 0.414 s
% 2.93/0.82  % (2602)------------------------------
% 2.93/0.82  % (2602)------------------------------
% 3.35/0.84  % (2640)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 3.35/0.86  % (2640)Refutation not found, incomplete strategy% (2640)------------------------------
% 3.35/0.86  % (2640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.56/0.87  % (2630)Refutation found. Thanks to Tanya!
% 3.56/0.87  % SZS status Theorem for theBenchmark
% 3.56/0.87  % (2640)Termination reason: Refutation not found, incomplete strategy
% 3.56/0.87  
% 3.56/0.87  % (2640)Memory used [KB]: 10746
% 3.56/0.87  % (2640)Time elapsed: 0.148 s
% 3.56/0.87  % (2640)------------------------------
% 3.56/0.87  % (2640)------------------------------
% 3.56/0.87  % SZS output start Proof for theBenchmark
% 3.56/0.87  fof(f2151,plain,(
% 3.56/0.87    $false),
% 3.56/0.87    inference(avatar_sat_refutation,[],[f103,f108,f112,f140,f148,f190,f375,f379,f400,f490,f527,f909,f982,f1101,f1432,f2116,f2149])).
% 3.56/0.87  fof(f2149,plain,(
% 3.56/0.87    spl6_2 | ~spl6_12 | ~spl6_40 | spl6_96 | ~spl6_120),
% 3.56/0.87    inference(avatar_contradiction_clause,[],[f2148])).
% 3.56/0.87  fof(f2148,plain,(
% 3.56/0.87    $false | (spl6_2 | ~spl6_12 | ~spl6_40 | spl6_96 | ~spl6_120)),
% 3.56/0.87    inference(subsumption_resolution,[],[f1431,f2147])).
% 3.56/0.87  fof(f2147,plain,(
% 3.56/0.87    r2_hidden(sK0,sK1) | (spl6_2 | ~spl6_12 | ~spl6_40 | ~spl6_120)),
% 3.56/0.87    inference(forward_demodulation,[],[f2118,f2119])).
% 3.56/0.87  fof(f2119,plain,(
% 3.56/0.87    sK0 = sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)) | (~spl6_12 | ~spl6_120)),
% 3.56/0.87    inference(unit_resulting_resolution,[],[f2115,f147])).
% 3.56/0.87  fof(f147,plain,(
% 3.56/0.87    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) ) | ~spl6_12),
% 3.56/0.87    inference(avatar_component_clause,[],[f146])).
% 3.56/0.87  fof(f146,plain,(
% 3.56/0.87    spl6_12 <=> ! [X3,X0] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0)))),
% 3.56/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 3.56/0.87  fof(f2115,plain,(
% 3.56/0.87    r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) | ~spl6_120),
% 3.56/0.87    inference(avatar_component_clause,[],[f2113])).
% 3.56/0.87  fof(f2113,plain,(
% 3.56/0.87    spl6_120 <=> r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 3.56/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_120])])).
% 3.56/0.87  fof(f2118,plain,(
% 3.56/0.87    r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),sK1) | (spl6_2 | ~spl6_40 | ~spl6_120)),
% 3.56/0.87    inference(unit_resulting_resolution,[],[f107,f2115,f2115,f399])).
% 3.56/0.87  fof(f399,plain,(
% 3.56/0.87    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) ) | ~spl6_40),
% 3.56/0.87    inference(avatar_component_clause,[],[f398])).
% 3.56/0.87  fof(f398,plain,(
% 3.56/0.87    spl6_40 <=> ! [X1,X0,X2] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2))),
% 3.56/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 3.56/0.87  fof(f107,plain,(
% 3.56/0.87    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) | spl6_2),
% 3.56/0.87    inference(avatar_component_clause,[],[f105])).
% 3.56/0.87  fof(f105,plain,(
% 3.56/0.87    spl6_2 <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 3.56/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 3.56/0.87  fof(f1431,plain,(
% 3.56/0.87    ~r2_hidden(sK0,sK1) | spl6_96),
% 3.56/0.87    inference(avatar_component_clause,[],[f1429])).
% 3.56/0.87  fof(f1429,plain,(
% 3.56/0.87    spl6_96 <=> r2_hidden(sK0,sK1)),
% 3.56/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_96])])).
% 3.56/0.87  fof(f2116,plain,(
% 3.56/0.87    spl6_120 | spl6_2 | ~spl6_84),
% 3.56/0.87    inference(avatar_split_clause,[],[f983,f980,f105,f2113])).
% 3.56/0.87  fof(f980,plain,(
% 3.56/0.87    spl6_84 <=> ! [X1,X0] : (r2_hidden(sK4(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0)),
% 3.56/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).
% 3.56/0.87  fof(f983,plain,(
% 3.56/0.87    r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) | (spl6_2 | ~spl6_84)),
% 3.56/0.87    inference(unit_resulting_resolution,[],[f107,f981])).
% 3.56/0.87  fof(f981,plain,(
% 3.56/0.87    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) ) | ~spl6_84),
% 3.56/0.87    inference(avatar_component_clause,[],[f980])).
% 3.56/0.87  fof(f1432,plain,(
% 3.56/0.87    ~spl6_96 | spl6_51 | ~spl6_87),
% 3.56/0.87    inference(avatar_split_clause,[],[f1315,f1098,f524,f1429])).
% 3.56/0.87  fof(f524,plain,(
% 3.56/0.87    spl6_51 <=> r2_hidden(sK4(k1_tarski(sK0),sK1,k1_xboole_0),sK1)),
% 3.56/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).
% 3.56/0.87  fof(f1098,plain,(
% 3.56/0.87    spl6_87 <=> sK0 = sK4(k1_tarski(sK0),sK1,k1_xboole_0)),
% 3.56/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).
% 3.56/0.87  fof(f1315,plain,(
% 3.56/0.87    ~r2_hidden(sK0,sK1) | (spl6_51 | ~spl6_87)),
% 3.56/0.87    inference(superposition,[],[f526,f1100])).
% 3.56/0.87  fof(f1100,plain,(
% 3.56/0.87    sK0 = sK4(k1_tarski(sK0),sK1,k1_xboole_0) | ~spl6_87),
% 3.56/0.87    inference(avatar_component_clause,[],[f1098])).
% 3.56/0.87  fof(f526,plain,(
% 3.56/0.87    ~r2_hidden(sK4(k1_tarski(sK0),sK1,k1_xboole_0),sK1) | spl6_51),
% 3.56/0.87    inference(avatar_component_clause,[],[f524])).
% 3.56/0.87  fof(f1101,plain,(
% 3.56/0.87    spl6_87 | ~spl6_12 | ~spl6_78),
% 3.56/0.87    inference(avatar_split_clause,[],[f943,f906,f146,f1098])).
% 3.56/0.87  fof(f906,plain,(
% 3.56/0.87    spl6_78 <=> r2_hidden(sK4(k1_tarski(sK0),sK1,k1_xboole_0),k1_tarski(sK0))),
% 3.56/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).
% 3.56/0.87  fof(f943,plain,(
% 3.56/0.87    sK0 = sK4(k1_tarski(sK0),sK1,k1_xboole_0) | (~spl6_12 | ~spl6_78)),
% 3.56/0.87    inference(unit_resulting_resolution,[],[f908,f147])).
% 3.56/0.87  fof(f908,plain,(
% 3.56/0.87    r2_hidden(sK4(k1_tarski(sK0),sK1,k1_xboole_0),k1_tarski(sK0)) | ~spl6_78),
% 3.56/0.87    inference(avatar_component_clause,[],[f906])).
% 3.56/0.87  fof(f982,plain,(
% 3.56/0.87    spl6_84 | ~spl6_36),
% 3.56/0.87    inference(avatar_split_clause,[],[f393,f373,f980])).
% 3.56/0.87  fof(f373,plain,(
% 3.56/0.87    spl6_36 <=> ! [X1,X0,X2] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))),
% 3.56/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 3.56/0.87  fof(f393,plain,(
% 3.56/0.87    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) ) | ~spl6_36),
% 3.56/0.87    inference(factoring,[],[f374])).
% 3.56/0.87  fof(f374,plain,(
% 3.56/0.87    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) ) | ~spl6_36),
% 3.56/0.87    inference(avatar_component_clause,[],[f373])).
% 3.56/0.87  fof(f909,plain,(
% 3.56/0.87    spl6_78 | spl6_1 | ~spl6_36 | ~spl6_49),
% 3.56/0.87    inference(avatar_split_clause,[],[f499,f488,f373,f100,f906])).
% 3.56/0.87  fof(f100,plain,(
% 3.56/0.87    spl6_1 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 3.56/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 3.56/0.87  fof(f488,plain,(
% 3.56/0.87    spl6_49 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 3.56/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 3.56/0.87  fof(f499,plain,(
% 3.56/0.87    r2_hidden(sK4(k1_tarski(sK0),sK1,k1_xboole_0),k1_tarski(sK0)) | (spl6_1 | ~spl6_36 | ~spl6_49)),
% 3.56/0.87    inference(unit_resulting_resolution,[],[f102,f489,f374])).
% 3.56/0.87  fof(f489,plain,(
% 3.56/0.87    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl6_49),
% 3.56/0.87    inference(avatar_component_clause,[],[f488])).
% 3.56/0.87  fof(f102,plain,(
% 3.56/0.87    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) | spl6_1),
% 3.56/0.87    inference(avatar_component_clause,[],[f100])).
% 3.56/0.87  fof(f527,plain,(
% 3.56/0.87    ~spl6_51 | spl6_1 | ~spl6_37 | ~spl6_49),
% 3.56/0.87    inference(avatar_split_clause,[],[f498,f488,f377,f100,f524])).
% 3.56/0.87  fof(f377,plain,(
% 3.56/0.87    spl6_37 <=> ! [X1,X0,X2] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2))),
% 3.56/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 3.56/0.88  fof(f498,plain,(
% 3.56/0.88    ~r2_hidden(sK4(k1_tarski(sK0),sK1,k1_xboole_0),sK1) | (spl6_1 | ~spl6_37 | ~spl6_49)),
% 3.56/0.88    inference(unit_resulting_resolution,[],[f102,f489,f378])).
% 3.56/0.88  fof(f378,plain,(
% 3.56/0.88    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X2)) ) | ~spl6_37),
% 3.56/0.88    inference(avatar_component_clause,[],[f377])).
% 3.56/0.88  fof(f490,plain,(
% 3.56/0.88    spl6_49 | ~spl6_3 | ~spl6_10 | ~spl6_20),
% 3.56/0.88    inference(avatar_split_clause,[],[f233,f188,f138,f110,f488])).
% 3.56/0.88  fof(f110,plain,(
% 3.56/0.88    spl6_3 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 3.56/0.88  fof(f138,plain,(
% 3.56/0.88    spl6_10 <=> ! [X1,X5,X2] : r2_hidden(X5,k1_enumset1(X5,X1,X2))),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 3.56/0.88  fof(f188,plain,(
% 3.56/0.88    spl6_20 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))),
% 3.56/0.88    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 3.56/0.88  fof(f233,plain,(
% 3.56/0.88    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl6_3 | ~spl6_10 | ~spl6_20)),
% 3.56/0.88    inference(unit_resulting_resolution,[],[f139,f111,f189])).
% 3.56/0.88  fof(f189,plain,(
% 3.56/0.88    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) ) | ~spl6_20),
% 3.56/0.88    inference(avatar_component_clause,[],[f188])).
% 3.56/0.88  fof(f111,plain,(
% 3.56/0.88    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl6_3),
% 3.56/0.88    inference(avatar_component_clause,[],[f110])).
% 3.56/0.88  fof(f139,plain,(
% 3.56/0.88    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) ) | ~spl6_10),
% 3.56/0.88    inference(avatar_component_clause,[],[f138])).
% 3.56/0.88  fof(f400,plain,(
% 3.56/0.88    spl6_40),
% 3.56/0.88    inference(avatar_split_clause,[],[f69,f398])).
% 3.56/0.88  fof(f69,plain,(
% 3.56/0.88    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 3.56/0.88    inference(cnf_transformation,[],[f38])).
% 3.56/0.88  fof(f38,plain,(
% 3.56/0.88    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.56/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 3.56/0.88  fof(f37,plain,(
% 3.56/0.88    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 3.56/0.88    introduced(choice_axiom,[])).
% 3.56/0.88  fof(f36,plain,(
% 3.56/0.88    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.56/0.88    inference(rectify,[],[f35])).
% 3.56/0.88  fof(f35,plain,(
% 3.56/0.88    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.56/0.88    inference(flattening,[],[f34])).
% 3.56/0.88  fof(f34,plain,(
% 3.56/0.88    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.56/0.88    inference(nnf_transformation,[],[f2])).
% 3.56/0.88  fof(f2,axiom,(
% 3.56/0.88    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.56/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 3.56/0.88  fof(f379,plain,(
% 3.56/0.88    spl6_37),
% 3.56/0.88    inference(avatar_split_clause,[],[f68,f377])).
% 3.56/0.88  fof(f68,plain,(
% 3.56/0.88    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 3.56/0.88    inference(cnf_transformation,[],[f38])).
% 3.56/0.88  fof(f375,plain,(
% 3.56/0.88    spl6_36),
% 3.56/0.88    inference(avatar_split_clause,[],[f67,f373])).
% 3.56/0.88  fof(f67,plain,(
% 3.56/0.88    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 3.56/0.88    inference(cnf_transformation,[],[f38])).
% 3.56/0.88  fof(f190,plain,(
% 3.56/0.88    spl6_20),
% 3.56/0.88    inference(avatar_split_clause,[],[f57,f188])).
% 3.56/0.88  fof(f57,plain,(
% 3.56/0.88    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.56/0.88    inference(cnf_transformation,[],[f29])).
% 3.56/0.88  fof(f29,plain,(
% 3.56/0.88    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.56/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f28])).
% 3.56/0.88  fof(f28,plain,(
% 3.56/0.88    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 3.56/0.88    introduced(choice_axiom,[])).
% 3.56/0.88  fof(f24,plain,(
% 3.56/0.88    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.56/0.88    inference(ennf_transformation,[],[f22])).
% 3.56/0.88  fof(f22,plain,(
% 3.56/0.88    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.56/0.88    inference(rectify,[],[f3])).
% 3.56/0.88  fof(f3,axiom,(
% 3.56/0.88    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.56/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 3.56/0.88  fof(f148,plain,(
% 3.56/0.88    spl6_12),
% 3.56/0.88    inference(avatar_split_clause,[],[f84,f146])).
% 3.56/0.88  fof(f84,plain,(
% 3.56/0.88    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 3.56/0.88    inference(equality_resolution,[],[f58])).
% 3.56/0.88  fof(f58,plain,(
% 3.56/0.88    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.56/0.88    inference(cnf_transformation,[],[f33])).
% 3.56/0.88  fof(f33,plain,(
% 3.56/0.88    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.56/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 3.56/0.88  fof(f32,plain,(
% 3.56/0.88    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 3.56/0.88    introduced(choice_axiom,[])).
% 3.56/0.88  fof(f31,plain,(
% 3.56/0.88    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.56/0.88    inference(rectify,[],[f30])).
% 3.56/0.88  fof(f30,plain,(
% 3.56/0.88    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.56/0.88    inference(nnf_transformation,[],[f11])).
% 3.56/0.88  fof(f11,axiom,(
% 3.56/0.88    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.56/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 3.56/0.88  fof(f140,plain,(
% 3.56/0.88    spl6_10),
% 3.56/0.88    inference(avatar_split_clause,[],[f93,f138])).
% 3.56/0.88  fof(f93,plain,(
% 3.56/0.88    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 3.56/0.88    inference(equality_resolution,[],[f92])).
% 3.56/0.88  fof(f92,plain,(
% 3.56/0.88    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 3.56/0.88    inference(equality_resolution,[],[f72])).
% 3.56/0.88  fof(f72,plain,(
% 3.56/0.88    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.56/0.88    inference(cnf_transformation,[],[f43])).
% 3.56/0.88  fof(f43,plain,(
% 3.56/0.88    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK5(X0,X1,X2,X3) != X2 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X2 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X0 | r2_hidden(sK5(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.56/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).
% 3.56/0.88  fof(f42,plain,(
% 3.56/0.88    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK5(X0,X1,X2,X3) != X2 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X2 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X0 | r2_hidden(sK5(X0,X1,X2,X3),X3))))),
% 3.56/0.88    introduced(choice_axiom,[])).
% 3.56/0.88  fof(f41,plain,(
% 3.56/0.88    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.56/0.88    inference(rectify,[],[f40])).
% 3.56/0.88  fof(f40,plain,(
% 3.56/0.88    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.56/0.88    inference(flattening,[],[f39])).
% 3.56/0.88  fof(f39,plain,(
% 3.56/0.88    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.56/0.88    inference(nnf_transformation,[],[f25])).
% 3.56/0.88  fof(f25,plain,(
% 3.56/0.88    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.56/0.88    inference(ennf_transformation,[],[f10])).
% 3.56/0.88  fof(f10,axiom,(
% 3.56/0.88    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.56/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 3.56/0.88  fof(f112,plain,(
% 3.56/0.88    spl6_3),
% 3.56/0.88    inference(avatar_split_clause,[],[f46,f110])).
% 3.56/0.88  fof(f46,plain,(
% 3.56/0.88    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.56/0.88    inference(cnf_transformation,[],[f6])).
% 3.56/0.88  fof(f6,axiom,(
% 3.56/0.88    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.56/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 3.56/0.88  fof(f108,plain,(
% 3.56/0.88    ~spl6_2),
% 3.56/0.88    inference(avatar_split_clause,[],[f45,f105])).
% 3.56/0.88  fof(f45,plain,(
% 3.56/0.88    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 3.56/0.88    inference(cnf_transformation,[],[f27])).
% 3.56/0.88  fof(f27,plain,(
% 3.56/0.88    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 3.56/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f26])).
% 3.56/0.88  fof(f26,plain,(
% 3.56/0.88    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1))),
% 3.56/0.88    introduced(choice_axiom,[])).
% 3.56/0.88  fof(f23,plain,(
% 3.56/0.88    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1))),
% 3.56/0.88    inference(ennf_transformation,[],[f21])).
% 3.56/0.88  fof(f21,negated_conjecture,(
% 3.56/0.88    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 3.56/0.88    inference(negated_conjecture,[],[f20])).
% 3.56/0.88  fof(f20,conjecture,(
% 3.56/0.88    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 3.56/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).
% 3.56/0.88  fof(f103,plain,(
% 3.56/0.88    ~spl6_1),
% 3.56/0.88    inference(avatar_split_clause,[],[f44,f100])).
% 3.56/0.88  fof(f44,plain,(
% 3.56/0.88    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 3.56/0.88    inference(cnf_transformation,[],[f27])).
% 3.56/0.88  % SZS output end Proof for theBenchmark
% 3.56/0.88  % (2630)------------------------------
% 3.56/0.88  % (2630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.56/0.88  % (2630)Termination reason: Refutation
% 3.56/0.88  
% 3.56/0.88  % (2630)Memory used [KB]: 8827
% 3.56/0.88  % (2630)Time elapsed: 0.318 s
% 3.56/0.88  % (2630)------------------------------
% 3.56/0.88  % (2630)------------------------------
% 3.56/0.88  % (2599)Success in time 0.509 s
%------------------------------------------------------------------------------
