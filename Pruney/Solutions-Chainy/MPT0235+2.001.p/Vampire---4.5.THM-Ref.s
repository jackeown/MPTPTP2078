%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:28 EST 2020

% Result     : Theorem 1.97s
% Output     : Refutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 153 expanded)
%              Number of leaves         :   12 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  290 ( 608 expanded)
%              Number of equality atoms :  141 ( 316 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1122,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f416,f760,f762,f1074,f1083,f1121])).

fof(f1121,plain,
    ( spl8_1
    | ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f1120])).

fof(f1120,plain,
    ( $false
    | spl8_1
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f1097,f187])).

fof(f187,plain,(
    ! [X1] : r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X1)) ),
    inference(equality_resolution,[],[f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X1))
      | k2_tarski(X1,X1) != X0 ) ),
    inference(definition_unfolding,[],[f120,f88,f88])).

fof(f88,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f120,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f1097,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))
    | spl8_1
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f1096,f182])).

fof(f182,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f55,f56])).

% (19030)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
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
    inference(rectify,[],[f54])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f1096,plain,
    ( ~ r2_hidden(k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0)))
    | spl8_1
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f411,f635])).

fof(f635,plain,
    ( k2_tarski(sK0,sK0) = sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0)))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f633])).

fof(f633,plain,
    ( spl8_9
  <=> k2_tarski(sK0,sK0) = sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f411,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))),k1_zfmisc_1(k2_tarski(sK0,sK0)))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f409])).

fof(f409,plain,
    ( spl8_1
  <=> r2_hidden(sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))),k1_zfmisc_1(k2_tarski(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f1083,plain,
    ( spl8_1
    | spl8_9
    | spl8_2 ),
    inference(avatar_split_clause,[],[f1082,f413,f633,f409])).

fof(f413,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1082,plain,
    ( k2_tarski(sK0,sK0) = sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0)))
    | r2_hidden(sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))),k1_zfmisc_1(k2_tarski(sK0,sK0)))
    | spl8_2 ),
    inference(subsumption_resolution,[],[f798,f150])).

fof(f150,plain,(
    k1_zfmisc_1(k2_tarski(sK0,sK0)) != k2_tarski(k1_xboole_0,k2_tarski(sK0,sK0)) ),
    inference(definition_unfolding,[],[f83,f88,f88])).

fof(f83,plain,(
    k1_zfmisc_1(k1_tarski(sK0)) != k2_tarski(k1_xboole_0,k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    k1_zfmisc_1(k1_tarski(sK0)) != k2_tarski(k1_xboole_0,k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f44])).

fof(f44,plain,
    ( ? [X0] : k1_zfmisc_1(k1_tarski(X0)) != k2_tarski(k1_xboole_0,k1_tarski(X0))
   => k1_zfmisc_1(k1_tarski(sK0)) != k2_tarski(k1_xboole_0,k1_tarski(sK0)) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0] : k1_zfmisc_1(k1_tarski(X0)) != k2_tarski(k1_xboole_0,k1_tarski(X0)) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,negated_conjecture,(
    ~ ! [X0] : k1_zfmisc_1(k1_tarski(X0)) = k2_tarski(k1_xboole_0,k1_tarski(X0)) ),
    inference(negated_conjecture,[],[f33])).

fof(f33,conjecture,(
    ! [X0] : k1_zfmisc_1(k1_tarski(X0)) = k2_tarski(k1_xboole_0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_zfmisc_1)).

fof(f798,plain,
    ( k1_zfmisc_1(k2_tarski(sK0,sK0)) = k2_tarski(k1_xboole_0,k2_tarski(sK0,sK0))
    | k2_tarski(sK0,sK0) = sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0)))
    | r2_hidden(sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))),k1_zfmisc_1(k2_tarski(sK0,sK0)))
    | spl8_2 ),
    inference(trivial_inequality_removal,[],[f796])).

fof(f796,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_zfmisc_1(k2_tarski(sK0,sK0)) = k2_tarski(k1_xboole_0,k2_tarski(sK0,sK0))
    | k2_tarski(sK0,sK0) = sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0)))
    | r2_hidden(sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))),k1_zfmisc_1(k2_tarski(sK0,sK0)))
    | spl8_2 ),
    inference(superposition,[],[f415,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK5(X0,X1,X2) = X1
      | sK5(X0,X1,X2) = X0
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK5(X0,X1,X2) != X1
              & sK5(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sK5(X0,X1,X2) = X1
            | sK5(X0,X1,X2) = X0
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f68,f69])).

fof(f69,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK5(X0,X1,X2) != X1
            & sK5(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sK5(X0,X1,X2) = X1
          | sK5(X0,X1,X2) = X0
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f415,plain,
    ( k1_xboole_0 != sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0)))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f413])).

fof(f1074,plain,
    ( ~ spl8_1
    | spl8_2
    | spl8_9 ),
    inference(avatar_contradiction_clause,[],[f1073])).

fof(f1073,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | spl8_9 ),
    inference(subsumption_resolution,[],[f1039,f881])).

fof(f881,plain,
    ( ~ r1_tarski(sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))),k2_tarski(sK0,sK0))
    | spl8_2
    | spl8_9 ),
    inference(unit_resulting_resolution,[],[f415,f634,f634,f634,f178])).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k2_tarski(X2,X2) = X0
      | k2_tarski(X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f145,f88,f88])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
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
    inference(flattening,[],[f81])).

fof(f81,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f634,plain,
    ( k2_tarski(sK0,sK0) != sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0)))
    | spl8_9 ),
    inference(avatar_component_clause,[],[f633])).

fof(f1039,plain,
    ( r1_tarski(sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))),k2_tarski(sK0,sK0))
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f410,f183])).

fof(f183,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f110])).

fof(f110,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f410,plain,
    ( r2_hidden(sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))),k1_zfmisc_1(k2_tarski(sK0,sK0)))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f409])).

fof(f762,plain,
    ( ~ spl8_1
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f456,f633,f409])).

fof(f456,plain,
    ( k2_tarski(sK0,sK0) != sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0)))
    | ~ r2_hidden(sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))),k1_zfmisc_1(k2_tarski(sK0,sK0))) ),
    inference(equality_resolution,[],[f235])).

fof(f235,plain,(
    ! [X3] :
      ( k1_zfmisc_1(k2_tarski(sK0,sK0)) != X3
      | k2_tarski(sK0,sK0) != sK5(k1_xboole_0,k2_tarski(sK0,sK0),X3)
      | ~ r2_hidden(sK5(k1_xboole_0,k2_tarski(sK0,sK0),X3),X3) ) ),
    inference(superposition,[],[f150,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK5(X0,X1,X2) != X1
      | ~ r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f760,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f759])).

fof(f759,plain,
    ( $false
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f729,f188])).

fof(f188,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k2_tarski(X1,X1)) ),
    inference(equality_resolution,[],[f164])).

fof(f164,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X1))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f119,f88])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f729,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_tarski(sK0,sK0))
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f637,f182])).

fof(f637,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k2_tarski(sK0,sK0)))
    | spl8_1
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f411,f414])).

fof(f414,plain,
    ( k1_xboole_0 = sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0)))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f413])).

fof(f416,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f405,f413,f409])).

fof(f405,plain,
    ( k1_xboole_0 != sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0)))
    | ~ r2_hidden(sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))),k1_zfmisc_1(k2_tarski(sK0,sK0))) ),
    inference(equality_resolution,[],[f234])).

fof(f234,plain,(
    ! [X2] :
      ( k1_zfmisc_1(k2_tarski(sK0,sK0)) != X2
      | k1_xboole_0 != sK5(k1_xboole_0,k2_tarski(sK0,sK0),X2)
      | ~ r2_hidden(sK5(k1_xboole_0,k2_tarski(sK0,sK0),X2),X2) ) ),
    inference(superposition,[],[f150,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK5(X0,X1,X2) != X0
      | ~ r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f70])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.51  % (18994)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (18985)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (18973)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (18970)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (18984)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (18994)Refutation not found, incomplete strategy% (18994)------------------------------
% 0.22/0.52  % (18994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (18994)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (18994)Memory used [KB]: 10746
% 0.22/0.52  % (18994)Time elapsed: 0.061 s
% 0.22/0.52  % (18994)------------------------------
% 0.22/0.52  % (18994)------------------------------
% 0.22/0.52  % (18982)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.29/0.52  % (18976)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.29/0.52  % (18981)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.29/0.52  % (19001)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.29/0.53  % (18986)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.29/0.53  % (18992)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.29/0.53  % (18977)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.29/0.53  % (18973)Refutation not found, incomplete strategy% (18973)------------------------------
% 1.29/0.53  % (18973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (18973)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (18973)Memory used [KB]: 10746
% 1.29/0.53  % (18973)Time elapsed: 0.127 s
% 1.29/0.53  % (18973)------------------------------
% 1.29/0.53  % (18973)------------------------------
% 1.35/0.53  % (18983)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.54  % (18975)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.35/0.54  % (19000)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.35/0.54  % (18974)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.35/0.54  % (18997)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.35/0.54  % (18981)Refutation not found, incomplete strategy% (18981)------------------------------
% 1.35/0.54  % (18981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (18981)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (18981)Memory used [KB]: 10618
% 1.35/0.54  % (18981)Time elapsed: 0.136 s
% 1.35/0.54  % (18981)------------------------------
% 1.35/0.54  % (18981)------------------------------
% 1.35/0.54  % (18995)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.35/0.54  % (18971)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.35/0.54  % (18989)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.35/0.54  % (18998)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.55  % (18999)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.55  % (18980)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.35/0.55  % (18987)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.35/0.55  % (18993)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.35/0.55  % (18991)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.55  % (18993)Refutation not found, incomplete strategy% (18993)------------------------------
% 1.35/0.55  % (18993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (18993)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (18993)Memory used [KB]: 1791
% 1.35/0.55  % (18993)Time elapsed: 0.149 s
% 1.35/0.55  % (18993)------------------------------
% 1.35/0.55  % (18993)------------------------------
% 1.35/0.55  % (18988)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.35/0.56  % (18978)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.35/0.56  % (18992)Refutation not found, incomplete strategy% (18992)------------------------------
% 1.35/0.56  % (18992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.56  % (18992)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.56  
% 1.35/0.56  % (18992)Memory used [KB]: 10746
% 1.35/0.56  % (18992)Time elapsed: 0.152 s
% 1.35/0.56  % (18992)------------------------------
% 1.35/0.56  % (18992)------------------------------
% 1.35/0.56  % (18979)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.35/0.56  % (18979)Refutation not found, incomplete strategy% (18979)------------------------------
% 1.35/0.56  % (18979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.56  % (18979)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.56  
% 1.35/0.56  % (18979)Memory used [KB]: 10746
% 1.35/0.56  % (18979)Time elapsed: 0.159 s
% 1.35/0.56  % (18979)------------------------------
% 1.35/0.56  % (18979)------------------------------
% 1.35/0.56  % (18996)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.97/0.64  % (19028)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.97/0.66  % (18998)Refutation found. Thanks to Tanya!
% 1.97/0.66  % SZS status Theorem for theBenchmark
% 1.97/0.66  % SZS output start Proof for theBenchmark
% 1.97/0.66  fof(f1122,plain,(
% 1.97/0.66    $false),
% 1.97/0.66    inference(avatar_sat_refutation,[],[f416,f760,f762,f1074,f1083,f1121])).
% 1.97/0.66  fof(f1121,plain,(
% 1.97/0.66    spl8_1 | ~spl8_9),
% 1.97/0.66    inference(avatar_contradiction_clause,[],[f1120])).
% 1.97/0.66  fof(f1120,plain,(
% 1.97/0.66    $false | (spl8_1 | ~spl8_9)),
% 1.97/0.66    inference(subsumption_resolution,[],[f1097,f187])).
% 1.97/0.66  fof(f187,plain,(
% 1.97/0.66    ( ! [X1] : (r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X1))) )),
% 1.97/0.66    inference(equality_resolution,[],[f163])).
% 1.97/0.66  fof(f163,plain,(
% 1.97/0.66    ( ! [X0,X1] : (r1_tarski(X0,k2_tarski(X1,X1)) | k2_tarski(X1,X1) != X0) )),
% 1.97/0.66    inference(definition_unfolding,[],[f120,f88,f88])).
% 1.97/0.66  fof(f88,plain,(
% 1.97/0.66    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.97/0.66    inference(cnf_transformation,[],[f23])).
% 1.97/0.66  fof(f23,axiom,(
% 1.97/0.66    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.97/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.97/0.66  fof(f120,plain,(
% 1.97/0.66    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) != X0) )),
% 1.97/0.66    inference(cnf_transformation,[],[f63])).
% 1.97/0.66  fof(f63,plain,(
% 1.97/0.66    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.97/0.66    inference(flattening,[],[f62])).
% 1.97/0.66  fof(f62,plain,(
% 1.97/0.66    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.97/0.66    inference(nnf_transformation,[],[f27])).
% 1.97/0.66  fof(f27,axiom,(
% 1.97/0.66    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.97/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.97/0.66  fof(f1097,plain,(
% 1.97/0.66    ~r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) | (spl8_1 | ~spl8_9)),
% 1.97/0.66    inference(unit_resulting_resolution,[],[f1096,f182])).
% 1.97/0.66  fof(f182,plain,(
% 1.97/0.66    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.97/0.66    inference(equality_resolution,[],[f111])).
% 1.97/0.66  fof(f111,plain,(
% 1.97/0.66    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.97/0.66    inference(cnf_transformation,[],[f57])).
% 1.97/0.66  fof(f57,plain,(
% 1.97/0.66    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.97/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f55,f56])).
% 1.97/0.68  % (19030)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 1.97/0.68  fof(f56,plain,(
% 1.97/0.68    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.97/0.68    introduced(choice_axiom,[])).
% 1.97/0.68  fof(f55,plain,(
% 1.97/0.68    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.97/0.68    inference(rectify,[],[f54])).
% 1.97/0.68  fof(f54,plain,(
% 1.97/0.68    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.97/0.68    inference(nnf_transformation,[],[f24])).
% 1.97/0.68  fof(f24,axiom,(
% 1.97/0.68    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.97/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.97/0.68  fof(f1096,plain,(
% 1.97/0.68    ~r2_hidden(k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))) | (spl8_1 | ~spl8_9)),
% 1.97/0.68    inference(forward_demodulation,[],[f411,f635])).
% 1.97/0.68  fof(f635,plain,(
% 1.97/0.68    k2_tarski(sK0,sK0) = sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))) | ~spl8_9),
% 1.97/0.68    inference(avatar_component_clause,[],[f633])).
% 1.97/0.68  fof(f633,plain,(
% 1.97/0.68    spl8_9 <=> k2_tarski(sK0,sK0) = sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0)))),
% 1.97/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.97/0.68  fof(f411,plain,(
% 1.97/0.68    ~r2_hidden(sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))),k1_zfmisc_1(k2_tarski(sK0,sK0))) | spl8_1),
% 1.97/0.68    inference(avatar_component_clause,[],[f409])).
% 1.97/0.68  fof(f409,plain,(
% 1.97/0.68    spl8_1 <=> r2_hidden(sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))),k1_zfmisc_1(k2_tarski(sK0,sK0)))),
% 1.97/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.97/0.68  fof(f1083,plain,(
% 1.97/0.68    spl8_1 | spl8_9 | spl8_2),
% 1.97/0.68    inference(avatar_split_clause,[],[f1082,f413,f633,f409])).
% 1.97/0.68  fof(f413,plain,(
% 1.97/0.68    spl8_2 <=> k1_xboole_0 = sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0)))),
% 1.97/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.97/0.68  fof(f1082,plain,(
% 1.97/0.68    k2_tarski(sK0,sK0) = sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))) | r2_hidden(sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))),k1_zfmisc_1(k2_tarski(sK0,sK0))) | spl8_2),
% 1.97/0.68    inference(subsumption_resolution,[],[f798,f150])).
% 1.97/0.68  fof(f150,plain,(
% 1.97/0.68    k1_zfmisc_1(k2_tarski(sK0,sK0)) != k2_tarski(k1_xboole_0,k2_tarski(sK0,sK0))),
% 1.97/0.68    inference(definition_unfolding,[],[f83,f88,f88])).
% 1.97/0.68  fof(f83,plain,(
% 1.97/0.68    k1_zfmisc_1(k1_tarski(sK0)) != k2_tarski(k1_xboole_0,k1_tarski(sK0))),
% 1.97/0.68    inference(cnf_transformation,[],[f45])).
% 1.97/0.68  fof(f45,plain,(
% 1.97/0.68    k1_zfmisc_1(k1_tarski(sK0)) != k2_tarski(k1_xboole_0,k1_tarski(sK0))),
% 1.97/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f44])).
% 1.97/0.68  fof(f44,plain,(
% 1.97/0.68    ? [X0] : k1_zfmisc_1(k1_tarski(X0)) != k2_tarski(k1_xboole_0,k1_tarski(X0)) => k1_zfmisc_1(k1_tarski(sK0)) != k2_tarski(k1_xboole_0,k1_tarski(sK0))),
% 1.97/0.68    introduced(choice_axiom,[])).
% 1.97/0.68  fof(f35,plain,(
% 1.97/0.68    ? [X0] : k1_zfmisc_1(k1_tarski(X0)) != k2_tarski(k1_xboole_0,k1_tarski(X0))),
% 1.97/0.68    inference(ennf_transformation,[],[f34])).
% 1.97/0.68  fof(f34,negated_conjecture,(
% 1.97/0.68    ~! [X0] : k1_zfmisc_1(k1_tarski(X0)) = k2_tarski(k1_xboole_0,k1_tarski(X0))),
% 1.97/0.68    inference(negated_conjecture,[],[f33])).
% 1.97/0.68  fof(f33,conjecture,(
% 1.97/0.68    ! [X0] : k1_zfmisc_1(k1_tarski(X0)) = k2_tarski(k1_xboole_0,k1_tarski(X0))),
% 1.97/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_zfmisc_1)).
% 1.97/0.68  fof(f798,plain,(
% 1.97/0.68    k1_zfmisc_1(k2_tarski(sK0,sK0)) = k2_tarski(k1_xboole_0,k2_tarski(sK0,sK0)) | k2_tarski(sK0,sK0) = sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))) | r2_hidden(sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))),k1_zfmisc_1(k2_tarski(sK0,sK0))) | spl8_2),
% 1.97/0.68    inference(trivial_inequality_removal,[],[f796])).
% 1.97/0.68  fof(f796,plain,(
% 1.97/0.68    k1_xboole_0 != k1_xboole_0 | k1_zfmisc_1(k2_tarski(sK0,sK0)) = k2_tarski(k1_xboole_0,k2_tarski(sK0,sK0)) | k2_tarski(sK0,sK0) = sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))) | r2_hidden(sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))),k1_zfmisc_1(k2_tarski(sK0,sK0))) | spl8_2),
% 1.97/0.68    inference(superposition,[],[f415,f130])).
% 1.97/0.68  fof(f130,plain,(
% 1.97/0.68    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 1.97/0.68    inference(cnf_transformation,[],[f70])).
% 1.97/0.68  fof(f70,plain,(
% 1.97/0.68    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.97/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f68,f69])).
% 1.97/0.68  fof(f69,plain,(
% 1.97/0.68    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.97/0.68    introduced(choice_axiom,[])).
% 1.97/0.68  fof(f68,plain,(
% 1.97/0.68    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.97/0.68    inference(rectify,[],[f67])).
% 1.97/0.68  fof(f67,plain,(
% 1.97/0.68    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.97/0.68    inference(flattening,[],[f66])).
% 1.97/0.68  fof(f66,plain,(
% 1.97/0.68    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.97/0.68    inference(nnf_transformation,[],[f22])).
% 1.97/0.68  fof(f22,axiom,(
% 1.97/0.68    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.97/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.97/0.68  fof(f415,plain,(
% 1.97/0.68    k1_xboole_0 != sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))) | spl8_2),
% 1.97/0.68    inference(avatar_component_clause,[],[f413])).
% 1.97/0.68  fof(f1074,plain,(
% 1.97/0.68    ~spl8_1 | spl8_2 | spl8_9),
% 1.97/0.68    inference(avatar_contradiction_clause,[],[f1073])).
% 1.97/0.68  fof(f1073,plain,(
% 1.97/0.68    $false | (~spl8_1 | spl8_2 | spl8_9)),
% 1.97/0.68    inference(subsumption_resolution,[],[f1039,f881])).
% 1.97/0.68  fof(f881,plain,(
% 1.97/0.68    ~r1_tarski(sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))),k2_tarski(sK0,sK0)) | (spl8_2 | spl8_9)),
% 1.97/0.68    inference(unit_resulting_resolution,[],[f415,f634,f634,f634,f178])).
% 1.97/0.68  fof(f178,plain,(
% 1.97/0.68    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k2_tarski(X2,X2) = X0 | k2_tarski(X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.97/0.68    inference(definition_unfolding,[],[f145,f88,f88])).
% 1.97/0.68  fof(f145,plain,(
% 1.97/0.68    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.97/0.68    inference(cnf_transformation,[],[f82])).
% 1.97/0.68  fof(f82,plain,(
% 1.97/0.68    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.97/0.68    inference(flattening,[],[f81])).
% 1.97/0.68  fof(f81,plain,(
% 1.97/0.68    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.97/0.68    inference(nnf_transformation,[],[f43])).
% 1.97/0.68  fof(f43,plain,(
% 1.97/0.68    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.97/0.68    inference(ennf_transformation,[],[f28])).
% 1.97/0.68  fof(f28,axiom,(
% 1.97/0.68    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.97/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 1.97/0.68  fof(f634,plain,(
% 1.97/0.68    k2_tarski(sK0,sK0) != sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))) | spl8_9),
% 1.97/0.68    inference(avatar_component_clause,[],[f633])).
% 1.97/0.68  fof(f1039,plain,(
% 1.97/0.68    r1_tarski(sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))),k2_tarski(sK0,sK0)) | ~spl8_1),
% 1.97/0.68    inference(unit_resulting_resolution,[],[f410,f183])).
% 1.97/0.68  fof(f183,plain,(
% 1.97/0.68    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.97/0.68    inference(equality_resolution,[],[f110])).
% 1.97/0.68  fof(f110,plain,(
% 1.97/0.68    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.97/0.68    inference(cnf_transformation,[],[f57])).
% 1.97/0.68  fof(f410,plain,(
% 1.97/0.68    r2_hidden(sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))),k1_zfmisc_1(k2_tarski(sK0,sK0))) | ~spl8_1),
% 1.97/0.68    inference(avatar_component_clause,[],[f409])).
% 1.97/0.68  fof(f762,plain,(
% 1.97/0.68    ~spl8_1 | ~spl8_9),
% 1.97/0.68    inference(avatar_split_clause,[],[f456,f633,f409])).
% 1.97/0.68  fof(f456,plain,(
% 1.97/0.68    k2_tarski(sK0,sK0) != sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))) | ~r2_hidden(sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))),k1_zfmisc_1(k2_tarski(sK0,sK0)))),
% 1.97/0.68    inference(equality_resolution,[],[f235])).
% 1.97/0.68  fof(f235,plain,(
% 1.97/0.68    ( ! [X3] : (k1_zfmisc_1(k2_tarski(sK0,sK0)) != X3 | k2_tarski(sK0,sK0) != sK5(k1_xboole_0,k2_tarski(sK0,sK0),X3) | ~r2_hidden(sK5(k1_xboole_0,k2_tarski(sK0,sK0),X3),X3)) )),
% 1.97/0.68    inference(superposition,[],[f150,f132])).
% 1.97/0.68  fof(f132,plain,(
% 1.97/0.68    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK5(X0,X1,X2) != X1 | ~r2_hidden(sK5(X0,X1,X2),X2)) )),
% 1.97/0.68    inference(cnf_transformation,[],[f70])).
% 1.97/0.68  fof(f760,plain,(
% 1.97/0.68    spl8_1 | ~spl8_2),
% 1.97/0.68    inference(avatar_contradiction_clause,[],[f759])).
% 1.97/0.68  fof(f759,plain,(
% 1.97/0.68    $false | (spl8_1 | ~spl8_2)),
% 1.97/0.68    inference(subsumption_resolution,[],[f729,f188])).
% 1.97/0.68  fof(f188,plain,(
% 1.97/0.68    ( ! [X1] : (r1_tarski(k1_xboole_0,k2_tarski(X1,X1))) )),
% 1.97/0.68    inference(equality_resolution,[],[f164])).
% 1.97/0.68  fof(f164,plain,(
% 1.97/0.68    ( ! [X0,X1] : (r1_tarski(X0,k2_tarski(X1,X1)) | k1_xboole_0 != X0) )),
% 1.97/0.68    inference(definition_unfolding,[],[f119,f88])).
% 1.97/0.68  fof(f119,plain,(
% 1.97/0.68    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 1.97/0.68    inference(cnf_transformation,[],[f63])).
% 1.97/0.68  fof(f729,plain,(
% 1.97/0.68    ~r1_tarski(k1_xboole_0,k2_tarski(sK0,sK0)) | (spl8_1 | ~spl8_2)),
% 1.97/0.68    inference(unit_resulting_resolution,[],[f637,f182])).
% 1.97/0.68  fof(f637,plain,(
% 1.97/0.68    ~r2_hidden(k1_xboole_0,k1_zfmisc_1(k2_tarski(sK0,sK0))) | (spl8_1 | ~spl8_2)),
% 1.97/0.68    inference(backward_demodulation,[],[f411,f414])).
% 1.97/0.68  fof(f414,plain,(
% 1.97/0.68    k1_xboole_0 = sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))) | ~spl8_2),
% 1.97/0.68    inference(avatar_component_clause,[],[f413])).
% 1.97/0.68  fof(f416,plain,(
% 1.97/0.68    ~spl8_1 | ~spl8_2),
% 1.97/0.68    inference(avatar_split_clause,[],[f405,f413,f409])).
% 1.97/0.68  fof(f405,plain,(
% 1.97/0.68    k1_xboole_0 != sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))) | ~r2_hidden(sK5(k1_xboole_0,k2_tarski(sK0,sK0),k1_zfmisc_1(k2_tarski(sK0,sK0))),k1_zfmisc_1(k2_tarski(sK0,sK0)))),
% 1.97/0.68    inference(equality_resolution,[],[f234])).
% 1.97/0.68  fof(f234,plain,(
% 1.97/0.68    ( ! [X2] : (k1_zfmisc_1(k2_tarski(sK0,sK0)) != X2 | k1_xboole_0 != sK5(k1_xboole_0,k2_tarski(sK0,sK0),X2) | ~r2_hidden(sK5(k1_xboole_0,k2_tarski(sK0,sK0),X2),X2)) )),
% 1.97/0.68    inference(superposition,[],[f150,f131])).
% 1.97/0.68  fof(f131,plain,(
% 1.97/0.68    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK5(X0,X1,X2) != X0 | ~r2_hidden(sK5(X0,X1,X2),X2)) )),
% 1.97/0.68    inference(cnf_transformation,[],[f70])).
% 1.97/0.68  % SZS output end Proof for theBenchmark
% 1.97/0.68  % (18998)------------------------------
% 1.97/0.68  % (18998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.68  % (18998)Termination reason: Refutation
% 1.97/0.68  
% 1.97/0.68  % (18998)Memory used [KB]: 11513
% 1.97/0.68  % (18998)Time elapsed: 0.241 s
% 1.97/0.68  % (18998)------------------------------
% 1.97/0.68  % (18998)------------------------------
% 1.97/0.68  % (18967)Success in time 0.315 s
%------------------------------------------------------------------------------
