%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0282+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:21 EST 2020

% Result     : Theorem 10.06s
% Output     : Refutation 10.06s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 183 expanded)
%              Number of leaves         :   19 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  310 ( 762 expanded)
%              Number of equality atoms :   30 (  88 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7095,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2438,f2448,f3155,f3175,f6923,f6933,f7046,f7052,f7094])).

fof(f7094,plain,
    ( ~ spl36_1
    | spl36_6 ),
    inference(avatar_contradiction_clause,[],[f7093])).

fof(f7093,plain,
    ( $false
    | ~ spl36_1
    | spl36_6 ),
    inference(subsumption_resolution,[],[f7078,f3208])).

fof(f3208,plain,
    ( ~ r2_hidden(sK13(k3_xboole_0(sK2,sK3),k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3))),k1_zfmisc_1(sK3))
    | spl36_6 ),
    inference(resolution,[],[f3154,f1255])).

fof(f1255,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f858])).

fof(f858,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f596])).

fof(f596,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK13(X0,X1),X0)
            | ~ r2_hidden(sK13(X0,X1),X1) )
          & ( r1_tarski(sK13(X0,X1),X0)
            | r2_hidden(sK13(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f594,f595])).

fof(f595,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK13(X0,X1),X0)
          | ~ r2_hidden(sK13(X0,X1),X1) )
        & ( r1_tarski(sK13(X0,X1),X0)
          | r2_hidden(sK13(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f594,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f593])).

fof(f593,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f284])).

fof(f284,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f3154,plain,
    ( ~ r1_tarski(sK13(k3_xboole_0(sK2,sK3),k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3))),sK3)
    | spl36_6 ),
    inference(avatar_component_clause,[],[f3152])).

fof(f3152,plain,
    ( spl36_6
  <=> r1_tarski(sK13(k3_xboole_0(sK2,sK3),k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_6])])).

fof(f7078,plain,
    ( r2_hidden(sK13(k3_xboole_0(sK2,sK3),k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3))),k1_zfmisc_1(sK3))
    | ~ spl36_1 ),
    inference(resolution,[],[f2432,f1278])).

fof(f1278,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f1025])).

fof(f1025,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f645])).

fof(f645,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK27(X0,X1,X2),X1)
            | ~ r2_hidden(sK27(X0,X1,X2),X0)
            | ~ r2_hidden(sK27(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK27(X0,X1,X2),X1)
              & r2_hidden(sK27(X0,X1,X2),X0) )
            | r2_hidden(sK27(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK27])],[f643,f644])).

fof(f644,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK27(X0,X1,X2),X1)
          | ~ r2_hidden(sK27(X0,X1,X2),X0)
          | ~ r2_hidden(sK27(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK27(X0,X1,X2),X1)
            & r2_hidden(sK27(X0,X1,X2),X0) )
          | r2_hidden(sK27(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f643,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f642])).

fof(f642,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f641])).

fof(f641,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f2432,plain,
    ( r2_hidden(sK13(k3_xboole_0(sK2,sK3),k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3))),k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3)))
    | ~ spl36_1 ),
    inference(avatar_component_clause,[],[f2431])).

fof(f2431,plain,
    ( spl36_1
  <=> r2_hidden(sK13(k3_xboole_0(sK2,sK3),k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3))),k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_1])])).

fof(f7052,plain,
    ( spl36_1
    | ~ spl36_2
    | ~ spl36_3 ),
    inference(avatar_contradiction_clause,[],[f7049])).

fof(f7049,plain,
    ( $false
    | spl36_1
    | ~ spl36_2
    | ~ spl36_3 ),
    inference(unit_resulting_resolution,[],[f2436,f2433,f3059,f1950])).

fof(f1950,plain,(
    ! [X33,X31,X32] :
      ( ~ r1_tarski(k1_zfmisc_1(X33),X32)
      | r2_hidden(X31,X32)
      | ~ r1_tarski(X31,X33) ) ),
    inference(resolution,[],[f849,f1254])).

fof(f1254,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f859])).

fof(f859,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f596])).

fof(f849,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f586])).

fof(f586,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f584,f585])).

fof(f585,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f584,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f583])).

fof(f583,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f435])).

fof(f435,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f3059,plain,
    ( r1_tarski(k1_zfmisc_1(k3_xboole_0(sK2,sK3)),k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3)))
    | ~ spl36_3 ),
    inference(avatar_component_clause,[],[f3058])).

fof(f3058,plain,
    ( spl36_3
  <=> r1_tarski(k1_zfmisc_1(k3_xboole_0(sK2,sK3)),k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_3])])).

fof(f2433,plain,
    ( ~ r2_hidden(sK13(k3_xboole_0(sK2,sK3),k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3))),k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3)))
    | spl36_1 ),
    inference(avatar_component_clause,[],[f2431])).

fof(f2436,plain,
    ( r1_tarski(sK13(k3_xboole_0(sK2,sK3),k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3))),k3_xboole_0(sK2,sK3))
    | ~ spl36_2 ),
    inference(avatar_component_clause,[],[f2435])).

fof(f2435,plain,
    ( spl36_2
  <=> r1_tarski(sK13(k3_xboole_0(sK2,sK3),k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3))),k3_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_2])])).

fof(f7046,plain,(
    spl36_8 ),
    inference(avatar_contradiction_clause,[],[f7045])).

fof(f7045,plain,
    ( $false
    | spl36_8 ),
    inference(subsumption_resolution,[],[f7030,f6950])).

fof(f6950,plain,
    ( ~ r1_tarski(k3_xboole_0(sK2,sK3),sK3)
    | spl36_8 ),
    inference(resolution,[],[f6922,f819])).

fof(f819,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f419])).

fof(f419,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f375])).

fof(f375,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f6922,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k3_xboole_0(sK2,sK3)),k1_zfmisc_1(sK3))
    | spl36_8 ),
    inference(avatar_component_clause,[],[f6920])).

fof(f6920,plain,
    ( spl36_8
  <=> r1_tarski(k1_zfmisc_1(k3_xboole_0(sK2,sK3)),k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_8])])).

fof(f7030,plain,
    ( r1_tarski(k3_xboole_0(sK2,sK3),sK3)
    | spl36_8 ),
    inference(resolution,[],[f6957,f851])).

fof(f851,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f586])).

fof(f6957,plain,
    ( r2_hidden(sK9(k3_xboole_0(sK2,sK3),sK3),sK3)
    | spl36_8 ),
    inference(resolution,[],[f6950,f1833])).

fof(f1833,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k3_xboole_0(X2,X3),X4)
      | r2_hidden(sK9(k3_xboole_0(X2,X3),X4),X3) ) ),
    inference(resolution,[],[f1278,f850])).

fof(f850,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f586])).

fof(f6933,plain,(
    spl36_7 ),
    inference(avatar_contradiction_clause,[],[f6932])).

fof(f6932,plain,
    ( $false
    | spl36_7 ),
    inference(subsumption_resolution,[],[f6925,f746])).

fof(f746,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f6925,plain,
    ( ~ r1_tarski(k3_xboole_0(sK2,sK3),sK2)
    | spl36_7 ),
    inference(resolution,[],[f6918,f819])).

fof(f6918,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k3_xboole_0(sK2,sK3)),k1_zfmisc_1(sK2))
    | spl36_7 ),
    inference(avatar_component_clause,[],[f6916])).

fof(f6916,plain,
    ( spl36_7
  <=> r1_tarski(k1_zfmisc_1(k3_xboole_0(sK2,sK3)),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_7])])).

fof(f6923,plain,
    ( ~ spl36_7
    | ~ spl36_8
    | spl36_3 ),
    inference(avatar_split_clause,[],[f3067,f3058,f6920,f6916])).

fof(f3067,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k3_xboole_0(sK2,sK3)),k1_zfmisc_1(sK3))
    | ~ r1_tarski(k1_zfmisc_1(k3_xboole_0(sK2,sK3)),k1_zfmisc_1(sK2))
    | spl36_3 ),
    inference(resolution,[],[f3060,f994])).

fof(f994,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f506])).

fof(f506,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f505])).

fof(f505,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f75])).

fof(f75,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f3060,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k3_xboole_0(sK2,sK3)),k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3)))
    | spl36_3 ),
    inference(avatar_component_clause,[],[f3058])).

fof(f3175,plain,
    ( ~ spl36_1
    | spl36_5 ),
    inference(avatar_contradiction_clause,[],[f3174])).

fof(f3174,plain,
    ( $false
    | ~ spl36_1
    | spl36_5 ),
    inference(subsumption_resolution,[],[f3172,f2450])).

fof(f2450,plain,
    ( r2_hidden(sK13(k3_xboole_0(sK2,sK3),k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3))),k1_zfmisc_1(sK2))
    | ~ spl36_1 ),
    inference(resolution,[],[f2432,f1279])).

fof(f1279,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f1024])).

fof(f1024,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f645])).

fof(f3172,plain,
    ( ~ r2_hidden(sK13(k3_xboole_0(sK2,sK3),k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3))),k1_zfmisc_1(sK2))
    | spl36_5 ),
    inference(resolution,[],[f3150,f1255])).

fof(f3150,plain,
    ( ~ r1_tarski(sK13(k3_xboole_0(sK2,sK3),k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3))),sK2)
    | spl36_5 ),
    inference(avatar_component_clause,[],[f3148])).

fof(f3148,plain,
    ( spl36_5
  <=> r1_tarski(sK13(k3_xboole_0(sK2,sK3),k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_5])])).

fof(f3155,plain,
    ( ~ spl36_5
    | ~ spl36_6
    | spl36_2 ),
    inference(avatar_split_clause,[],[f2440,f2435,f3152,f3148])).

fof(f2440,plain,
    ( ~ r1_tarski(sK13(k3_xboole_0(sK2,sK3),k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3))),sK3)
    | ~ r1_tarski(sK13(k3_xboole_0(sK2,sK3),k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3))),sK2)
    | spl36_2 ),
    inference(resolution,[],[f2437,f994])).

fof(f2437,plain,
    ( ~ r1_tarski(sK13(k3_xboole_0(sK2,sK3),k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3))),k3_xboole_0(sK2,sK3))
    | spl36_2 ),
    inference(avatar_component_clause,[],[f2435])).

fof(f2448,plain,
    ( spl36_1
    | spl36_2 ),
    inference(avatar_contradiction_clause,[],[f2447])).

fof(f2447,plain,
    ( $false
    | spl36_1
    | spl36_2 ),
    inference(unit_resulting_resolution,[],[f1347,f2437,f2433,f1439])).

fof(f1439,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK13(X0,X1),X0)
      | sQ35_eqProxy(k1_zfmisc_1(X0),X1)
      | r2_hidden(sK13(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f860,f1331])).

fof(f1331,plain,(
    ! [X1,X0] :
      ( sQ35_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ35_eqProxy])])).

fof(f860,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
      | r1_tarski(sK13(X0,X1),X0)
      | r2_hidden(sK13(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f596])).

fof(f1347,plain,(
    ~ sQ35_eqProxy(k1_zfmisc_1(k3_xboole_0(sK2,sK3)),k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3))) ),
    inference(equality_proxy_replacement,[],[f702,f1331])).

fof(f702,plain,(
    k1_zfmisc_1(k3_xboole_0(sK2,sK3)) != k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f561])).

fof(f561,plain,(
    k1_zfmisc_1(k3_xboole_0(sK2,sK3)) != k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f389,f560])).

fof(f560,plain,
    ( ? [X0,X1] : k1_zfmisc_1(k3_xboole_0(X0,X1)) != k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
   => k1_zfmisc_1(k3_xboole_0(sK2,sK3)) != k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3)) ),
    introduced(choice_axiom,[])).

fof(f389,plain,(
    ? [X0,X1] : k1_zfmisc_1(k3_xboole_0(X0,X1)) != k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
    inference(ennf_transformation,[],[f380])).

fof(f380,negated_conjecture,(
    ~ ! [X0,X1] : k1_zfmisc_1(k3_xboole_0(X0,X1)) = k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
    inference(negated_conjecture,[],[f379])).

fof(f379,conjecture,(
    ! [X0,X1] : k1_zfmisc_1(k3_xboole_0(X0,X1)) = k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_zfmisc_1)).

fof(f2438,plain,
    ( ~ spl36_1
    | ~ spl36_2 ),
    inference(avatar_split_clause,[],[f1757,f2435,f2431])).

fof(f1757,plain,
    ( ~ r1_tarski(sK13(k3_xboole_0(sK2,sK3),k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3))),k3_xboole_0(sK2,sK3))
    | ~ r2_hidden(sK13(k3_xboole_0(sK2,sK3),k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3))),k3_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3))) ),
    inference(resolution,[],[f1438,f1347])).

fof(f1438,plain,(
    ! [X0,X1] :
      ( sQ35_eqProxy(k1_zfmisc_1(X0),X1)
      | ~ r1_tarski(sK13(X0,X1),X0)
      | ~ r2_hidden(sK13(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f861,f1331])).

fof(f861,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
      | ~ r1_tarski(sK13(X0,X1),X0)
      | ~ r2_hidden(sK13(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f596])).
%------------------------------------------------------------------------------
