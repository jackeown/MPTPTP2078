%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0326+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:24 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   47 (  88 expanded)
%              Number of leaves         :   11 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :  127 ( 287 expanded)
%              Number of equality atoms :   19 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1161,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f816,f1087,f1105,f1113,f1160])).

fof(f1160,plain,(
    ~ spl25_10 ),
    inference(avatar_contradiction_clause,[],[f1129])).

fof(f1129,plain,
    ( $false
    | ~ spl25_10 ),
    inference(resolution,[],[f943,f601])).

fof(f601,plain,(
    ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f536])).

fof(f536,plain,
    ( ~ r1_tarski(sK1,sK3)
    & ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
      | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) )
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f433,f535,f534])).

fof(f534,plain,
    ( ? [X0] :
        ( ? [X1,X2,X3] :
            ( ~ r1_tarski(X1,X3)
            & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X3,X2,X1] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f535,plain,
    ( ? [X3,X2,X1] :
        ( ~ r1_tarski(X1,X3)
        & ( r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2))
          | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)) ) )
   => ( ~ r1_tarski(sK1,sK3)
      & ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
        | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f433,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f351])).

fof(f351,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1,X2,X3] :
            ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
           => r1_tarski(X1,X3) ) ) ),
    inference(negated_conjecture,[],[f350])).

fof(f350,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1,X2,X3] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
         => r1_tarski(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).

fof(f943,plain,
    ( ! [X8] : r1_tarski(sK1,X8)
    | ~ spl25_10 ),
    inference(avatar_component_clause,[],[f942])).

fof(f942,plain,
    ( spl25_10
  <=> ! [X8] : r1_tarski(sK1,X8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_10])])).

fof(f1113,plain,(
    ~ spl25_9 ),
    inference(avatar_contradiction_clause,[],[f1112])).

fof(f1112,plain,
    ( $false
    | ~ spl25_9 ),
    inference(subsumption_resolution,[],[f1111,f782])).

fof(f782,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1111,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl25_9 ),
    inference(backward_demodulation,[],[f599,f940])).

fof(f940,plain,
    ( k1_xboole_0 = sK0
    | ~ spl25_9 ),
    inference(avatar_component_clause,[],[f938])).

fof(f938,plain,
    ( spl25_9
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_9])])).

fof(f599,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f536])).

fof(f1105,plain,
    ( spl25_9
    | spl25_10
    | ~ spl25_2 ),
    inference(avatar_split_clause,[],[f936,f813,f942,f938])).

fof(f813,plain,
    ( spl25_2
  <=> r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_2])])).

fof(f936,plain,
    ( ! [X8] :
        ( r1_tarski(sK1,X8)
        | k1_xboole_0 = sK0 )
    | ~ spl25_2 ),
    inference(subsumption_resolution,[],[f881,f702])).

fof(f702,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f881,plain,
    ( ! [X8] :
        ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X8,sK0))
        | r1_tarski(sK1,X8)
        | k1_xboole_0 = sK0 )
    | ~ spl25_2 ),
    inference(superposition,[],[f613,f834])).

fof(f834,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK0)
    | ~ spl25_2 ),
    inference(subsumption_resolution,[],[f817,f601])).

fof(f817,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK0)
    | r1_tarski(sK1,sK3)
    | ~ spl25_2 ),
    inference(resolution,[],[f815,f609])).

fof(f609,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f448])).

fof(f448,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f447])).

fof(f447,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f349])).

fof(f349,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f815,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
    | ~ spl25_2 ),
    inference(avatar_component_clause,[],[f813])).

fof(f613,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f451])).

fof(f451,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f328])).

fof(f328,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f1087,plain,
    ( spl25_9
    | spl25_10
    | ~ spl25_1 ),
    inference(avatar_split_clause,[],[f1086,f809,f942,f938])).

fof(f809,plain,
    ( spl25_1
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_1])])).

fof(f1086,plain,
    ( ! [X10] :
        ( r1_tarski(sK1,X10)
        | k1_xboole_0 = sK0 )
    | ~ spl25_1 ),
    inference(subsumption_resolution,[],[f1029,f702])).

fof(f1029,plain,
    ( ! [X10] :
        ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,X10))
        | r1_tarski(sK1,X10)
        | k1_xboole_0 = sK0 )
    | ~ spl25_1 ),
    inference(superposition,[],[f614,f1012])).

fof(f1012,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl25_1 ),
    inference(subsumption_resolution,[],[f996,f601])).

fof(f996,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | r1_tarski(sK1,sK3)
    | ~ spl25_1 ),
    inference(resolution,[],[f811,f610])).

fof(f610,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | r1_tarski(X1,X3) ) ),
    inference(cnf_transformation,[],[f448])).

fof(f811,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl25_1 ),
    inference(avatar_component_clause,[],[f809])).

fof(f614,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f451])).

fof(f816,plain,
    ( spl25_1
    | spl25_2 ),
    inference(avatar_split_clause,[],[f600,f813,f809])).

fof(f600,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f536])).
%------------------------------------------------------------------------------
