%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0247+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 149 expanded)
%              Number of leaves         :   14 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  255 ( 631 expanded)
%              Number of equality atoms :  114 ( 370 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1614,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f909,f925,f929,f933,f938,f1304,f1569,f1596,f1613])).

fof(f1613,plain,
    ( spl21_1
    | ~ spl21_3 ),
    inference(avatar_contradiction_clause,[],[f1612])).

fof(f1612,plain,
    ( $false
    | spl21_1
    | ~ spl21_3 ),
    inference(subsumption_resolution,[],[f1606,f1605])).

fof(f1605,plain,
    ( r2_hidden(sK18(sK4,sK4),sK4)
    | spl21_1
    | ~ spl21_3 ),
    inference(backward_demodulation,[],[f916,f937])).

fof(f937,plain,
    ( sK4 = k2_tarski(sK5,sK6)
    | ~ spl21_3 ),
    inference(avatar_component_clause,[],[f923])).

fof(f923,plain,
    ( spl21_3
  <=> sK4 = k2_tarski(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_3])])).

fof(f916,plain,
    ( r2_hidden(sK18(sK4,k2_tarski(sK5,sK6)),sK4)
    | spl21_1 ),
    inference(resolution,[],[f905,f713])).

fof(f713,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK18(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f530])).

fof(f530,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK18(X0,X1),X1)
          & r2_hidden(sK18(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f528,f529])).

fof(f529,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK18(X0,X1),X1)
        & r2_hidden(sK18(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f528,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f527])).

fof(f527,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f426])).

fof(f426,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f905,plain,
    ( ~ r1_tarski(sK4,k2_tarski(sK5,sK6))
    | spl21_1 ),
    inference(avatar_component_clause,[],[f904])).

fof(f904,plain,
    ( spl21_1
  <=> r1_tarski(sK4,k2_tarski(sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_1])])).

fof(f1606,plain,
    ( ~ r2_hidden(sK18(sK4,sK4),sK4)
    | spl21_1
    | ~ spl21_3 ),
    inference(backward_demodulation,[],[f917,f937])).

fof(f917,plain,
    ( ~ r2_hidden(sK18(sK4,k2_tarski(sK5,sK6)),k2_tarski(sK5,sK6))
    | spl21_1 ),
    inference(resolution,[],[f905,f714])).

fof(f714,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK18(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f530])).

fof(f1596,plain,
    ( spl21_1
    | ~ spl21_2 ),
    inference(avatar_contradiction_clause,[],[f1595])).

fof(f1595,plain,
    ( $false
    | spl21_1
    | ~ spl21_2 ),
    inference(subsumption_resolution,[],[f1582,f582])).

fof(f582,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1582,plain,
    ( ! [X3] : ~ r1_tarski(k1_xboole_0,k4_xboole_0(k2_tarski(sK5,sK6),X3))
    | spl21_1
    | ~ spl21_2 ),
    inference(backward_demodulation,[],[f915,f934])).

fof(f934,plain,
    ( k1_xboole_0 = sK4
    | ~ spl21_2 ),
    inference(avatar_component_clause,[],[f907])).

fof(f907,plain,
    ( spl21_2
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_2])])).

fof(f915,plain,
    ( ! [X3] : ~ r1_tarski(sK4,k4_xboole_0(k2_tarski(sK5,sK6),X3))
    | spl21_1 ),
    inference(resolution,[],[f905,f632])).

fof(f632,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f405])).

fof(f405,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f54])).

fof(f54,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f1569,plain,
    ( spl21_1
    | ~ spl21_5 ),
    inference(avatar_contradiction_clause,[],[f1497])).

fof(f1497,plain,
    ( $false
    | spl21_1
    | ~ spl21_5 ),
    inference(resolution,[],[f1358,f905])).

fof(f1358,plain,
    ( ! [X41] : r1_tarski(sK4,k2_tarski(sK5,X41))
    | ~ spl21_5 ),
    inference(superposition,[],[f807,f935])).

fof(f935,plain,
    ( sK4 = k2_tarski(sK5,sK5)
    | ~ spl21_5 ),
    inference(avatar_component_clause,[],[f931])).

fof(f931,plain,
    ( spl21_5
  <=> sK4 = k2_tarski(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_5])])).

fof(f807,plain,(
    ! [X0,X1] : r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f610,f611])).

fof(f611,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f610,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f312])).

fof(f312,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f1304,plain,
    ( spl21_1
    | ~ spl21_4 ),
    inference(avatar_contradiction_clause,[],[f1235])).

fof(f1235,plain,
    ( $false
    | spl21_1
    | ~ spl21_4 ),
    inference(resolution,[],[f1008,f905])).

fof(f1008,plain,
    ( ! [X72] : r1_tarski(sK4,k2_tarski(X72,sK6))
    | ~ spl21_4 ),
    inference(superposition,[],[f880,f936])).

fof(f936,plain,
    ( sK4 = k2_tarski(sK6,sK6)
    | ~ spl21_4 ),
    inference(avatar_component_clause,[],[f927])).

fof(f927,plain,
    ( spl21_4
  <=> sK4 = k2_tarski(sK6,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_4])])).

fof(f880,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X2,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f779])).

fof(f779,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X2,X2) != X0 ) ),
    inference(definition_unfolding,[],[f548,f611])).

fof(f548,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f468])).

fof(f468,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f467])).

fof(f467,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f356])).

fof(f356,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f307])).

fof(f307,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f938,plain,
    ( spl21_2
    | spl21_5
    | spl21_4
    | spl21_3 ),
    inference(avatar_split_clause,[],[f902,f923,f927,f931,f907])).

fof(f902,plain,
    ( sK4 = k2_tarski(sK5,sK6)
    | sK4 = k2_tarski(sK6,sK6)
    | sK4 = k2_tarski(sK5,sK5)
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f775,f781])).

fof(f781,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k2_tarski(X2,X2) = X0
      | k2_tarski(X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f545,f611,f611])).

fof(f545,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f468])).

fof(f775,plain,
    ( sK4 = k2_tarski(sK5,sK6)
    | sK4 = k2_tarski(sK6,sK6)
    | sK4 = k2_tarski(sK5,sK5)
    | k1_xboole_0 = sK4
    | r1_tarski(sK4,k2_tarski(sK5,sK6)) ),
    inference(definition_unfolding,[],[f537,f611,f611])).

fof(f537,plain,
    ( sK4 = k2_tarski(sK5,sK6)
    | sK4 = k1_tarski(sK6)
    | sK4 = k1_tarski(sK5)
    | k1_xboole_0 = sK4
    | r1_tarski(sK4,k2_tarski(sK5,sK6)) ),
    inference(cnf_transformation,[],[f466])).

fof(f466,plain,
    ( ( ( sK4 != k2_tarski(sK5,sK6)
        & sK4 != k1_tarski(sK6)
        & sK4 != k1_tarski(sK5)
        & k1_xboole_0 != sK4 )
      | ~ r1_tarski(sK4,k2_tarski(sK5,sK6)) )
    & ( sK4 = k2_tarski(sK5,sK6)
      | sK4 = k1_tarski(sK6)
      | sK4 = k1_tarski(sK5)
      | k1_xboole_0 = sK4
      | r1_tarski(sK4,k2_tarski(sK5,sK6)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f464,f465])).

fof(f465,plain,
    ( ? [X0,X1,X2] :
        ( ( ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 )
          | ~ r1_tarski(X0,k2_tarski(X1,X2)) )
        & ( k2_tarski(X1,X2) = X0
          | k1_tarski(X2) = X0
          | k1_tarski(X1) = X0
          | k1_xboole_0 = X0
          | r1_tarski(X0,k2_tarski(X1,X2)) ) )
   => ( ( ( sK4 != k2_tarski(sK5,sK6)
          & sK4 != k1_tarski(sK6)
          & sK4 != k1_tarski(sK5)
          & k1_xboole_0 != sK4 )
        | ~ r1_tarski(sK4,k2_tarski(sK5,sK6)) )
      & ( sK4 = k2_tarski(sK5,sK6)
        | sK4 = k1_tarski(sK6)
        | sK4 = k1_tarski(sK5)
        | k1_xboole_0 = sK4
        | r1_tarski(sK4,k2_tarski(sK5,sK6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f464,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f463])).

fof(f463,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f352])).

fof(f352,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f344])).

fof(f344,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k2_tarski(X1,X2))
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f343])).

fof(f343,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_zfmisc_1)).

fof(f933,plain,
    ( ~ spl21_1
    | ~ spl21_5 ),
    inference(avatar_split_clause,[],[f774,f931,f904])).

fof(f774,plain,
    ( sK4 != k2_tarski(sK5,sK5)
    | ~ r1_tarski(sK4,k2_tarski(sK5,sK6)) ),
    inference(definition_unfolding,[],[f539,f611])).

fof(f539,plain,
    ( sK4 != k1_tarski(sK5)
    | ~ r1_tarski(sK4,k2_tarski(sK5,sK6)) ),
    inference(cnf_transformation,[],[f466])).

fof(f929,plain,
    ( ~ spl21_1
    | ~ spl21_4 ),
    inference(avatar_split_clause,[],[f773,f927,f904])).

fof(f773,plain,
    ( sK4 != k2_tarski(sK6,sK6)
    | ~ r1_tarski(sK4,k2_tarski(sK5,sK6)) ),
    inference(definition_unfolding,[],[f540,f611])).

fof(f540,plain,
    ( sK4 != k1_tarski(sK6)
    | ~ r1_tarski(sK4,k2_tarski(sK5,sK6)) ),
    inference(cnf_transformation,[],[f466])).

fof(f925,plain,
    ( ~ spl21_1
    | ~ spl21_3 ),
    inference(avatar_split_clause,[],[f541,f923,f904])).

fof(f541,plain,
    ( sK4 != k2_tarski(sK5,sK6)
    | ~ r1_tarski(sK4,k2_tarski(sK5,sK6)) ),
    inference(cnf_transformation,[],[f466])).

fof(f909,plain,
    ( ~ spl21_1
    | ~ spl21_2 ),
    inference(avatar_split_clause,[],[f538,f907,f904])).

fof(f538,plain,
    ( k1_xboole_0 != sK4
    | ~ r1_tarski(sK4,k2_tarski(sK5,sK6)) ),
    inference(cnf_transformation,[],[f466])).
%------------------------------------------------------------------------------
