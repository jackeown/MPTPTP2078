%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0379+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:52 EST 2020

% Result     : Theorem 2.08s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 277 expanded)
%              Number of leaves         :   47 ( 140 expanded)
%              Depth                    :   11
%              Number of atoms          :  623 (1845 expanded)
%              Number of equality atoms :  243 ( 412 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1167,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f100,f104,f108,f112,f116,f120,f124,f128,f143,f149,f155,f163,f188,f934,f1055,f1078,f1079,f1080,f1081,f1082,f1083,f1084,f1165])).

fof(f1165,plain,
    ( ~ spl11_10
    | ~ spl11_18 ),
    inference(avatar_contradiction_clause,[],[f1164])).

fof(f1164,plain,
    ( $false
    | ~ spl11_10
    | ~ spl11_18 ),
    inference(resolution,[],[f1102,f195])).

fof(f195,plain,
    ( ! [X4] : r1_tarski(k1_xboole_0,X4)
    | ~ spl11_10
    | ~ spl11_18 ),
    inference(forward_demodulation,[],[f192,f187])).

fof(f187,plain,
    ( k1_xboole_0 = k1_zfmisc_1(sK0)
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl11_18
  <=> k1_xboole_0 = k1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f192,plain,
    ( ! [X4] : r1_tarski(k1_zfmisc_1(sK0),X4)
    | ~ spl11_10 ),
    inference(resolution,[],[f183,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f183,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_zfmisc_1(sK0))
    | ~ spl11_10 ),
    inference(resolution,[],[f139,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f139,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl11_10
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f1102,plain,
    ( ! [X1] : ~ r1_tarski(X1,sK0)
    | ~ spl11_10
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f203,f200])).

fof(f200,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl11_10
    | ~ spl11_18 ),
    inference(superposition,[],[f183,f187])).

fof(f203,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k1_xboole_0)
        | ~ r1_tarski(X1,sK0) )
    | ~ spl11_18 ),
    inference(superposition,[],[f76,f187])).

fof(f76,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK9(X0,X1),X0)
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( r1_tarski(sK9(X0,X1),X0)
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK9(X0,X1),X0)
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( r1_tarski(sK9(X0,X1),X0)
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f1084,plain,
    ( sK5 != sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | ~ m1_subset_1(sK5,sK0)
    | m1_subset_1(sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1083,plain,
    ( sK4 != sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | ~ m1_subset_1(sK4,sK0)
    | m1_subset_1(sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1082,plain,
    ( sK3 != sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | ~ m1_subset_1(sK3,sK0)
    | m1_subset_1(sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1081,plain,
    ( sK2 != sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | ~ m1_subset_1(sK2,sK0)
    | m1_subset_1(sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1080,plain,
    ( sK1 != sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | ~ m1_subset_1(sK1,sK0)
    | m1_subset_1(sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1079,plain,
    ( sK7 != sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | ~ m1_subset_1(sK7,sK0)
    | m1_subset_1(sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1078,plain,
    ( sK6 != sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | ~ m1_subset_1(sK6,sK0)
    | m1_subset_1(sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1055,plain,
    ( spl11_95
    | spl11_96
    | spl11_97
    | spl11_98
    | spl11_99
    | spl11_100
    | spl11_101
    | spl11_12 ),
    inference(avatar_split_clause,[],[f1020,f147,f1053,f1050,f1047,f1044,f1041,f1038,f1035])).

fof(f1035,plain,
    ( spl11_95
  <=> sK6 = sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_95])])).

fof(f1038,plain,
    ( spl11_96
  <=> sK7 = sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_96])])).

fof(f1041,plain,
    ( spl11_97
  <=> sK1 = sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_97])])).

fof(f1044,plain,
    ( spl11_98
  <=> sK2 = sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_98])])).

fof(f1047,plain,
    ( spl11_99
  <=> sK3 = sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_99])])).

fof(f1050,plain,
    ( spl11_100
  <=> sK4 = sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_100])])).

fof(f1053,plain,
    ( spl11_101
  <=> sK5 = sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_101])])).

fof(f147,plain,
    ( spl11_12
  <=> r1_tarski(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f1020,plain,
    ( sK5 = sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | sK4 = sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | sK3 = sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | sK2 = sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | sK1 = sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | sK7 = sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | sK6 = sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | spl11_12 ),
    inference(resolution,[],[f716,f148])).

fof(f148,plain,
    ( ~ r1_tarski(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | spl11_12 ),
    inference(avatar_component_clause,[],[f147])).

fof(f716,plain,(
    ! [X70,X68,X66,X72,X71,X69,X67,X73] :
      ( r1_tarski(k5_enumset1(X67,X68,X69,X70,X71,X66,X72),X73)
      | sK8(k5_enumset1(X67,X68,X69,X70,X71,X66,X72),X73) = X71
      | sK8(k5_enumset1(X67,X68,X69,X70,X71,X66,X72),X73) = X70
      | sK8(k5_enumset1(X67,X68,X69,X70,X71,X66,X72),X73) = X69
      | sK8(k5_enumset1(X67,X68,X69,X70,X71,X66,X72),X73) = X68
      | sK8(k5_enumset1(X67,X68,X69,X70,X71,X66,X72),X73) = X67
      | sK8(k5_enumset1(X67,X68,X69,X70,X71,X66,X72),X73) = X72
      | sK8(k5_enumset1(X67,X68,X69,X70,X71,X66,X72),X73) = X66 ) ),
    inference(resolution,[],[f92,f53])).

fof(f92,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1,X9] :
      ( ~ r2_hidden(X9,k5_enumset1(X0,X1,X2,X3,X4,X5,X6))
      | X5 = X9
      | X4 = X9
      | X3 = X9
      | X2 = X9
      | X1 = X9
      | X0 = X9
      | X6 = X9 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( X6 = X9
      | X5 = X9
      | X4 = X9
      | X3 = X9
      | X2 = X9
      | X1 = X9
      | X0 = X9
      | ~ r2_hidden(X9,X7)
      | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
        | ( ( ( sK10(X0,X1,X2,X3,X4,X5,X6,X7) != X6
              & sK10(X0,X1,X2,X3,X4,X5,X6,X7) != X5
              & sK10(X0,X1,X2,X3,X4,X5,X6,X7) != X4
              & sK10(X0,X1,X2,X3,X4,X5,X6,X7) != X3
              & sK10(X0,X1,X2,X3,X4,X5,X6,X7) != X2
              & sK10(X0,X1,X2,X3,X4,X5,X6,X7) != X1
              & sK10(X0,X1,X2,X3,X4,X5,X6,X7) != X0 )
            | ~ r2_hidden(sK10(X0,X1,X2,X3,X4,X5,X6,X7),X7) )
          & ( sK10(X0,X1,X2,X3,X4,X5,X6,X7) = X6
            | sK10(X0,X1,X2,X3,X4,X5,X6,X7) = X5
            | sK10(X0,X1,X2,X3,X4,X5,X6,X7) = X4
            | sK10(X0,X1,X2,X3,X4,X5,X6,X7) = X3
            | sK10(X0,X1,X2,X3,X4,X5,X6,X7) = X2
            | sK10(X0,X1,X2,X3,X4,X5,X6,X7) = X1
            | sK10(X0,X1,X2,X3,X4,X5,X6,X7) = X0
            | r2_hidden(sK10(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X7)
              | ( X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 ) )
            & ( X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | ~ r2_hidden(X9,X7) ) )
        | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f35,f36])).

fof(f36,plain,(
    ! [X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( ( ( X6 != X8
              & X5 != X8
              & X4 != X8
              & X3 != X8
              & X2 != X8
              & X1 != X8
              & X0 != X8 )
            | ~ r2_hidden(X8,X7) )
          & ( X6 = X8
            | X5 = X8
            | X4 = X8
            | X3 = X8
            | X2 = X8
            | X1 = X8
            | X0 = X8
            | r2_hidden(X8,X7) ) )
     => ( ( ( sK10(X0,X1,X2,X3,X4,X5,X6,X7) != X6
            & sK10(X0,X1,X2,X3,X4,X5,X6,X7) != X5
            & sK10(X0,X1,X2,X3,X4,X5,X6,X7) != X4
            & sK10(X0,X1,X2,X3,X4,X5,X6,X7) != X3
            & sK10(X0,X1,X2,X3,X4,X5,X6,X7) != X2
            & sK10(X0,X1,X2,X3,X4,X5,X6,X7) != X1
            & sK10(X0,X1,X2,X3,X4,X5,X6,X7) != X0 )
          | ~ r2_hidden(sK10(X0,X1,X2,X3,X4,X5,X6,X7),X7) )
        & ( sK10(X0,X1,X2,X3,X4,X5,X6,X7) = X6
          | sK10(X0,X1,X2,X3,X4,X5,X6,X7) = X5
          | sK10(X0,X1,X2,X3,X4,X5,X6,X7) = X4
          | sK10(X0,X1,X2,X3,X4,X5,X6,X7) = X3
          | sK10(X0,X1,X2,X3,X4,X5,X6,X7) = X2
          | sK10(X0,X1,X2,X3,X4,X5,X6,X7) = X1
          | sK10(X0,X1,X2,X3,X4,X5,X6,X7) = X0
          | r2_hidden(sK10(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
        | ? [X8] :
            ( ( ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 )
              | ~ r2_hidden(X8,X7) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X7)
              | ( X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 ) )
            & ( X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | ~ r2_hidden(X9,X7) ) )
        | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
        | ? [X8] :
            ( ( ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 )
              | ~ r2_hidden(X8,X7) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X7)
              | ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 ) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | ~ r2_hidden(X8,X7) ) )
        | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
        | ? [X8] :
            ( ( ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 )
              | ~ r2_hidden(X8,X7) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X7)
              | ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 ) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | ~ r2_hidden(X8,X7) ) )
        | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ( X6 = X8
            | X5 = X8
            | X4 = X8
            | X3 = X8
            | X2 = X8
            | X1 = X8
            | X0 = X8 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X6 != X8
              & X5 != X8
              & X4 != X8
              & X3 != X8
              & X2 != X8
              & X1 != X8
              & X0 != X8 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_enumset1)).

fof(f934,plain,
    ( spl11_2
    | ~ spl11_14 ),
    inference(avatar_split_clause,[],[f930,f158,f98])).

fof(f98,plain,
    ( spl11_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f158,plain,
    ( spl11_14
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f930,plain,
    ( k1_xboole_0 = sK0
    | ~ spl11_14 ),
    inference(resolution,[],[f159,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f159,plain,
    ( v1_xboole_0(sK0)
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f158])).

fof(f188,plain,
    ( spl11_18
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f184,f138,f186])).

fof(f184,plain,
    ( k1_xboole_0 = k1_zfmisc_1(sK0)
    | ~ spl11_10 ),
    inference(resolution,[],[f139,f47])).

fof(f163,plain,
    ( spl11_14
    | ~ spl11_15
    | spl11_13 ),
    inference(avatar_split_clause,[],[f156,f153,f161,f158])).

fof(f161,plain,
    ( spl11_15
  <=> m1_subset_1(sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f153,plain,
    ( spl11_13
  <=> r2_hidden(sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f156,plain,
    ( ~ m1_subset_1(sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0),sK0)
    | v1_xboole_0(sK0)
    | spl11_13 ),
    inference(resolution,[],[f154,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f154,plain,
    ( ~ r2_hidden(sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0),sK0)
    | spl11_13 ),
    inference(avatar_component_clause,[],[f153])).

fof(f155,plain,
    ( ~ spl11_13
    | spl11_12 ),
    inference(avatar_split_clause,[],[f151,f147,f153])).

fof(f151,plain,
    ( ~ r2_hidden(sK8(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0),sK0)
    | spl11_12 ),
    inference(resolution,[],[f54,f148])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK8(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f149,plain,
    ( ~ spl11_12
    | spl11_11 ),
    inference(avatar_split_clause,[],[f144,f141,f147])).

fof(f141,plain,
    ( spl11_11
  <=> r2_hidden(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f144,plain,
    ( ~ r1_tarski(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),sK0)
    | spl11_11 ),
    inference(resolution,[],[f142,f76])).

fof(f142,plain,
    ( ~ r2_hidden(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(sK0))
    | spl11_11 ),
    inference(avatar_component_clause,[],[f141])).

fof(f143,plain,
    ( spl11_10
    | ~ spl11_11
    | spl11_1 ),
    inference(avatar_split_clause,[],[f136,f94,f141,f138])).

fof(f94,plain,
    ( spl11_1
  <=> m1_subset_1(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f136,plain,
    ( ~ r2_hidden(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | spl11_1 ),
    inference(resolution,[],[f49,f95])).

fof(f95,plain,
    ( ~ m1_subset_1(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(sK0))
    | spl11_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f128,plain,(
    spl11_9 ),
    inference(avatar_split_clause,[],[f38,f126])).

fof(f126,plain,
    ( spl11_9
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f38,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ m1_subset_1(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(sK0))
    & k1_xboole_0 != sK0
    & m1_subset_1(sK7,sK0)
    & m1_subset_1(sK6,sK0)
    & m1_subset_1(sK5,sK0)
    & m1_subset_1(sK4,sK0)
    & m1_subset_1(sK3,sK0)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f10,f22,f21,f20,f19,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
                                & k1_xboole_0 != X0
                                & m1_subset_1(X7,X0) )
                            & m1_subset_1(X6,X0) )
                        & m1_subset_1(X5,X0) )
                    & m1_subset_1(X4,X0) )
                & m1_subset_1(X3,X0) )
            & m1_subset_1(X2,X0) )
        & m1_subset_1(X1,X0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ~ m1_subset_1(k5_enumset1(sK1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(sK0))
                              & k1_xboole_0 != sK0
                              & m1_subset_1(X7,sK0) )
                          & m1_subset_1(X6,sK0) )
                      & m1_subset_1(X5,sK0) )
                  & m1_subset_1(X4,sK0) )
              & m1_subset_1(X3,sK0) )
          & m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ~ m1_subset_1(k5_enumset1(sK1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(sK0))
                            & k1_xboole_0 != sK0
                            & m1_subset_1(X7,sK0) )
                        & m1_subset_1(X6,sK0) )
                    & m1_subset_1(X5,sK0) )
                & m1_subset_1(X4,sK0) )
            & m1_subset_1(X3,sK0) )
        & m1_subset_1(X2,sK0) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ~ m1_subset_1(k5_enumset1(sK1,sK2,X3,X4,X5,X6,X7),k1_zfmisc_1(sK0))
                          & k1_xboole_0 != sK0
                          & m1_subset_1(X7,sK0) )
                      & m1_subset_1(X6,sK0) )
                  & m1_subset_1(X5,sK0) )
              & m1_subset_1(X4,sK0) )
          & m1_subset_1(X3,sK0) )
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ~ m1_subset_1(k5_enumset1(sK1,sK2,X3,X4,X5,X6,X7),k1_zfmisc_1(sK0))
                        & k1_xboole_0 != sK0
                        & m1_subset_1(X7,sK0) )
                    & m1_subset_1(X6,sK0) )
                & m1_subset_1(X5,sK0) )
            & m1_subset_1(X4,sK0) )
        & m1_subset_1(X3,sK0) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ~ m1_subset_1(k5_enumset1(sK1,sK2,sK3,X4,X5,X6,X7),k1_zfmisc_1(sK0))
                      & k1_xboole_0 != sK0
                      & m1_subset_1(X7,sK0) )
                  & m1_subset_1(X6,sK0) )
              & m1_subset_1(X5,sK0) )
          & m1_subset_1(X4,sK0) )
      & m1_subset_1(sK3,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ~ m1_subset_1(k5_enumset1(sK1,sK2,sK3,X4,X5,X6,X7),k1_zfmisc_1(sK0))
                    & k1_xboole_0 != sK0
                    & m1_subset_1(X7,sK0) )
                & m1_subset_1(X6,sK0) )
            & m1_subset_1(X5,sK0) )
        & m1_subset_1(X4,sK0) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ~ m1_subset_1(k5_enumset1(sK1,sK2,sK3,sK4,X5,X6,X7),k1_zfmisc_1(sK0))
                  & k1_xboole_0 != sK0
                  & m1_subset_1(X7,sK0) )
              & m1_subset_1(X6,sK0) )
          & m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ? [X7] :
                ( ~ m1_subset_1(k5_enumset1(sK1,sK2,sK3,sK4,X5,X6,X7),k1_zfmisc_1(sK0))
                & k1_xboole_0 != sK0
                & m1_subset_1(X7,sK0) )
            & m1_subset_1(X6,sK0) )
        & m1_subset_1(X5,sK0) )
   => ( ? [X6] :
          ( ? [X7] :
              ( ~ m1_subset_1(k5_enumset1(sK1,sK2,sK3,sK4,sK5,X6,X7),k1_zfmisc_1(sK0))
              & k1_xboole_0 != sK0
              & m1_subset_1(X7,sK0) )
          & m1_subset_1(X6,sK0) )
      & m1_subset_1(sK5,sK0) ) ),
    introduced(choice_axiom,[])).

% (5745)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
fof(f21,plain,
    ( ? [X6] :
        ( ? [X7] :
            ( ~ m1_subset_1(k5_enumset1(sK1,sK2,sK3,sK4,sK5,X6,X7),k1_zfmisc_1(sK0))
            & k1_xboole_0 != sK0
            & m1_subset_1(X7,sK0) )
        & m1_subset_1(X6,sK0) )
   => ( ? [X7] :
          ( ~ m1_subset_1(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,X7),k1_zfmisc_1(sK0))
          & k1_xboole_0 != sK0
          & m1_subset_1(X7,sK0) )
      & m1_subset_1(sK6,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X7] :
        ( ~ m1_subset_1(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,X7),k1_zfmisc_1(sK0))
        & k1_xboole_0 != sK0
        & m1_subset_1(X7,sK0) )
   => ( ~ m1_subset_1(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(sK0))
      & k1_xboole_0 != sK0
      & m1_subset_1(sK7,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
                              & k1_xboole_0 != X0
                              & m1_subset_1(X7,X0) )
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ~ m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
                              & k1_xboole_0 != X0
                              & m1_subset_1(X7,X0) )
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ! [X2] :
            ( m1_subset_1(X2,X0)
           => ! [X3] :
                ( m1_subset_1(X3,X0)
               => ! [X4] :
                    ( m1_subset_1(X4,X0)
                   => ! [X5] :
                        ( m1_subset_1(X5,X0)
                       => ! [X6] :
                            ( m1_subset_1(X6,X0)
                           => ! [X7] :
                                ( m1_subset_1(X7,X0)
                               => ( k1_xboole_0 != X0
                                 => m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ! [X3] :
              ( m1_subset_1(X3,X0)
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ! [X5] :
                      ( m1_subset_1(X5,X0)
                     => ! [X6] :
                          ( m1_subset_1(X6,X0)
                         => ! [X7] :
                              ( m1_subset_1(X7,X0)
                             => ( k1_xboole_0 != X0
                               => m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_subset_1)).

fof(f124,plain,(
    spl11_8 ),
    inference(avatar_split_clause,[],[f39,f122])).

fof(f122,plain,
    ( spl11_8
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f39,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f120,plain,(
    spl11_7 ),
    inference(avatar_split_clause,[],[f40,f118])).

fof(f118,plain,
    ( spl11_7
  <=> m1_subset_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f40,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f116,plain,(
    spl11_6 ),
    inference(avatar_split_clause,[],[f41,f114])).

fof(f114,plain,
    ( spl11_6
  <=> m1_subset_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f41,plain,(
    m1_subset_1(sK4,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f112,plain,(
    spl11_5 ),
    inference(avatar_split_clause,[],[f42,f110])).

fof(f110,plain,
    ( spl11_5
  <=> m1_subset_1(sK5,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f42,plain,(
    m1_subset_1(sK5,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f108,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f43,f106])).

fof(f106,plain,
    ( spl11_4
  <=> m1_subset_1(sK6,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f43,plain,(
    m1_subset_1(sK6,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f104,plain,(
    spl11_3 ),
    inference(avatar_split_clause,[],[f44,f102])).

fof(f102,plain,
    ( spl11_3
  <=> m1_subset_1(sK7,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f44,plain,(
    m1_subset_1(sK7,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f100,plain,(
    ~ spl11_2 ),
    inference(avatar_split_clause,[],[f45,f98])).

fof(f45,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f23])).

fof(f96,plain,(
    ~ spl11_1 ),
    inference(avatar_split_clause,[],[f46,f94])).

fof(f46,plain,(
    ~ m1_subset_1(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

%------------------------------------------------------------------------------
