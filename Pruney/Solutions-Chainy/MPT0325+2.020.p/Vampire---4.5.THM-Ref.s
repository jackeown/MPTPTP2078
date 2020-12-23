%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:40 EST 2020

% Result     : Theorem 35.14s
% Output     : Refutation 35.14s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 351 expanded)
%              Number of leaves         :   29 ( 128 expanded)
%              Depth                    :   13
%              Number of atoms          :  257 ( 588 expanded)
%              Number of equality atoms :   66 ( 265 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f88734,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f65,f70,f1382,f1387,f10057,f83743,f83748,f83756,f84250,f84267,f88568,f88733])).

fof(f88733,plain,
    ( ~ spl6_43
    | spl6_7
    | ~ spl6_65 ),
    inference(avatar_split_clause,[],[f88662,f88565,f1384,f84247])).

fof(f84247,plain,
    ( spl6_43
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f1384,plain,
    ( spl6_7
  <=> r1_tarski(k2_zfmisc_1(sK0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f88565,plain,
    ( spl6_65
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f88662,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl6_7
    | ~ spl6_65 ),
    inference(forward_demodulation,[],[f88661,f57290])).

fof(f57290,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f57289,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f57289,plain,(
    ! [X0,X1] : k1_xboole_0 = k2_zfmisc_1(X0,k5_xboole_0(X1,X1)) ),
    inference(forward_demodulation,[],[f57288,f35])).

fof(f35,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f57288,plain,(
    ! [X0,X1] : k1_xboole_0 = k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1))) ),
    inference(forward_demodulation,[],[f57172,f33])).

fof(f57172,plain,(
    ! [X0,X1] : k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1))) = k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) ),
    inference(superposition,[],[f49,f35])).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f45,f39,f39])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f88661,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),k1_xboole_0)
    | spl6_7
    | ~ spl6_65 ),
    inference(forward_demodulation,[],[f88660,f57290])).

fof(f88660,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),k2_zfmisc_1(sK2,k1_xboole_0))
    | spl6_7
    | ~ spl6_65 ),
    inference(forward_demodulation,[],[f88606,f57290])).

fof(f88606,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k2_zfmisc_1(sK0,k1_xboole_0)),k2_zfmisc_1(sK2,k2_zfmisc_1(sK0,k1_xboole_0)))
    | spl6_7
    | ~ spl6_65 ),
    inference(superposition,[],[f1386,f88567])).

fof(f88567,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_65 ),
    inference(avatar_component_clause,[],[f88565])).

fof(f1386,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,k2_zfmisc_1(sK0,sK1)))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f1384])).

fof(f88568,plain,
    ( spl6_65
    | spl6_2
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f88560,f83745,f58,f88565])).

fof(f58,plain,
    ( spl6_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f83745,plain,
    ( spl6_36
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f88560,plain,
    ( k1_xboole_0 = sK1
    | spl6_2
    | ~ spl6_36 ),
    inference(unit_resulting_resolution,[],[f60,f83747,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f83747,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f83745])).

fof(f60,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f84267,plain,(
    spl6_43 ),
    inference(avatar_contradiction_clause,[],[f84253])).

fof(f84253,plain,
    ( $false
    | spl6_43 ),
    inference(unit_resulting_resolution,[],[f112,f84249])).

fof(f84249,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl6_43 ),
    inference(avatar_component_clause,[],[f84247])).

fof(f112,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(superposition,[],[f36,f97])).

fof(f97,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f89,f34])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f89,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f81,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f81,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f77,f33])).

fof(f77,plain,(
    ! [X0] : r1_xboole_0(X0,k5_xboole_0(X0,X0)) ),
    inference(superposition,[],[f38,f35])).

fof(f38,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f84250,plain,
    ( ~ spl6_43
    | spl6_1
    | spl6_3
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f84241,f83753,f62,f52,f84247])).

fof(f52,plain,
    ( spl6_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f62,plain,
    ( spl6_3
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f83753,plain,
    ( spl6_37
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f84241,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl6_1
    | spl6_3
    | ~ spl6_37 ),
    inference(forward_demodulation,[],[f84240,f57290])).

fof(f84240,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,k1_xboole_0),k1_xboole_0)
    | spl6_1
    | spl6_3
    | ~ spl6_37 ),
    inference(forward_demodulation,[],[f84239,f57290])).

fof(f84239,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,k1_xboole_0),k2_zfmisc_1(sK3,k1_xboole_0))
    | spl6_1
    | spl6_3
    | ~ spl6_37 ),
    inference(forward_demodulation,[],[f84238,f79607])).

fof(f79607,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f79606,f33])).

fof(f79606,plain,(
    ! [X0,X1] : k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f79605,f33])).

fof(f79605,plain,(
    ! [X0,X1] : k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(k5_xboole_0(X0,X0),X1) ),
    inference(forward_demodulation,[],[f79604,f35])).

fof(f79604,plain,(
    ! [X0,X1] : k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X0)),X1) ),
    inference(forward_demodulation,[],[f79448,f35])).

fof(f79448,plain,(
    ! [X0,X1] : k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X0)),X1) = k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,k3_xboole_0(X1,X1))) ),
    inference(superposition,[],[f50,f27592])).

fof(f27592,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f48,f35])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f44,f39,f39])).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f84238,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,k2_zfmisc_1(k1_xboole_0,sK1)),k2_zfmisc_1(sK3,k2_zfmisc_1(k1_xboole_0,sK1)))
    | spl6_1
    | spl6_3
    | ~ spl6_37 ),
    inference(forward_demodulation,[],[f84237,f83755])).

fof(f83755,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f83753])).

fof(f84237,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK3,k2_zfmisc_1(sK0,sK1)))
    | spl6_1
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f54,f64,f46])).

fof(f64,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f54,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f83756,plain,
    ( spl6_37
    | spl6_3
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f83750,f83740,f62,f83753])).

fof(f83740,plain,
    ( spl6_35
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f83750,plain,
    ( r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK0
    | ~ spl6_35 ),
    inference(resolution,[],[f83742,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f83742,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f83740])).

fof(f83748,plain,
    ( spl6_36
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f83712,f10054,f83745])).

fof(f10054,plain,
    ( spl6_15
  <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f83712,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | ~ spl6_15 ),
    inference(superposition,[],[f80534,f10056])).

fof(f10056,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f10054])).

fof(f80534,plain,(
    ! [X24,X23,X25,X22] : r1_tarski(k3_xboole_0(k2_zfmisc_1(X22,X23),k2_zfmisc_1(X25,X24)),k2_zfmisc_1(X22,X24)) ),
    inference(forward_demodulation,[],[f80249,f48])).

fof(f80249,plain,(
    ! [X24,X23,X25,X22] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X22,X25),k3_xboole_0(X23,X24)),k2_zfmisc_1(X22,X24)) ),
    inference(superposition,[],[f75862,f27649])).

fof(f27649,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0) ),
    inference(superposition,[],[f48,f35])).

fof(f75862,plain,(
    ! [X6,X4,X5,X3] : r1_tarski(k3_xboole_0(k2_zfmisc_1(X4,k3_xboole_0(X5,X6)),X3),k2_zfmisc_1(X4,X6)) ),
    inference(superposition,[],[f74822,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f74822,plain,(
    ! [X130,X128,X131,X129] : r1_tarski(k3_xboole_0(X131,k2_zfmisc_1(X128,k3_xboole_0(X129,X130))),k2_zfmisc_1(X128,X130)) ),
    inference(superposition,[],[f478,f27592])).

fof(f478,plain,(
    ! [X23,X21,X22] : r1_tarski(k3_xboole_0(X21,k3_xboole_0(X22,X23)),X23) ),
    inference(superposition,[],[f72,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f72,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f36,f37])).

fof(f83743,plain,
    ( spl6_35
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f83711,f1379,f83740])).

fof(f1379,plain,
    ( spl6_6
  <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f83711,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))
    | ~ spl6_6 ),
    inference(superposition,[],[f80534,f1381])).

fof(f1381,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f1379])).

fof(f10057,plain,
    ( spl6_15
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f1399,f1379,f10054])).

fof(f1399,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_6 ),
    inference(superposition,[],[f186,f1381])).

fof(f186,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f139,f37])).

fof(f139,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X1) ),
    inference(unit_resulting_resolution,[],[f72,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1387,plain,
    ( ~ spl6_7
    | spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f1223,f58,f52,f1384])).

fof(f1223,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,k2_zfmisc_1(sK0,sK1)))
    | spl6_1
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f60,f54,f46])).

fof(f1382,plain,
    ( spl6_6
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f138,f67,f1379])).

fof(f67,plain,
    ( spl6_4
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f138,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f69,f42])).

fof(f69,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f70,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f30,f67])).

fof(f30,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ r1_tarski(sK1,sK3)
      | ~ r1_tarski(sK0,sK2) )
    & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1)
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK1,sK3)
        | ~ r1_tarski(sK0,sK2) )
      & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
      & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f65,plain,
    ( ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f32,f62,f58])).

fof(f32,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f31,f52])).

fof(f31,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:34:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.41  % (1689)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.45  % (1676)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.45  % (1677)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.45  % (1675)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (1690)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (1681)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (1682)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (1685)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (1679)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (1683)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (1680)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  % (1678)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (1693)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.50  % (1692)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.50  % (1691)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.50  % (1686)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.50  % (1687)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.50  % (1688)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 4.96/1.03  % (1679)Time limit reached!
% 4.96/1.03  % (1679)------------------------------
% 4.96/1.03  % (1679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.96/1.03  % (1679)Termination reason: Time limit
% 4.96/1.03  % (1679)Termination phase: Saturation
% 4.96/1.03  
% 4.96/1.03  % (1679)Memory used [KB]: 13432
% 4.96/1.03  % (1679)Time elapsed: 0.600 s
% 4.96/1.03  % (1679)------------------------------
% 4.96/1.03  % (1679)------------------------------
% 12.66/1.97  % (1680)Time limit reached!
% 12.66/1.97  % (1680)------------------------------
% 12.66/1.97  % (1680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.66/1.97  % (1680)Termination reason: Time limit
% 12.66/1.97  
% 12.66/1.97  % (1680)Memory used [KB]: 25202
% 12.66/1.97  % (1680)Time elapsed: 1.548 s
% 12.66/1.97  % (1680)------------------------------
% 12.66/1.97  % (1680)------------------------------
% 12.98/1.98  % (1681)Time limit reached!
% 12.98/1.98  % (1681)------------------------------
% 12.98/1.98  % (1681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.98/1.98  % (1681)Termination reason: Time limit
% 12.98/1.98  
% 12.98/1.98  % (1681)Memory used [KB]: 32366
% 12.98/1.98  % (1681)Time elapsed: 1.516 s
% 12.98/1.98  % (1681)------------------------------
% 12.98/1.98  % (1681)------------------------------
% 14.46/2.23  % (1677)Time limit reached!
% 14.46/2.23  % (1677)------------------------------
% 14.46/2.23  % (1677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.46/2.23  % (1677)Termination reason: Time limit
% 14.46/2.23  
% 14.46/2.23  % (1677)Memory used [KB]: 40169
% 14.46/2.23  % (1677)Time elapsed: 1.823 s
% 14.46/2.23  % (1677)------------------------------
% 14.46/2.23  % (1677)------------------------------
% 17.85/2.60  % (1688)Time limit reached!
% 17.85/2.60  % (1688)------------------------------
% 17.85/2.60  % (1688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.85/2.60  % (1688)Termination reason: Time limit
% 17.85/2.60  % (1688)Termination phase: Saturation
% 17.85/2.60  
% 17.85/2.60  % (1688)Memory used [KB]: 40681
% 17.85/2.60  % (1688)Time elapsed: 2.200 s
% 17.85/2.60  % (1688)------------------------------
% 17.85/2.60  % (1688)------------------------------
% 35.14/4.80  % (1693)Refutation found. Thanks to Tanya!
% 35.14/4.80  % SZS status Theorem for theBenchmark
% 35.14/4.81  % SZS output start Proof for theBenchmark
% 35.14/4.81  fof(f88734,plain,(
% 35.14/4.81    $false),
% 35.14/4.81    inference(avatar_sat_refutation,[],[f55,f65,f70,f1382,f1387,f10057,f83743,f83748,f83756,f84250,f84267,f88568,f88733])).
% 35.14/4.81  fof(f88733,plain,(
% 35.14/4.81    ~spl6_43 | spl6_7 | ~spl6_65),
% 35.14/4.81    inference(avatar_split_clause,[],[f88662,f88565,f1384,f84247])).
% 35.14/4.81  fof(f84247,plain,(
% 35.14/4.81    spl6_43 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 35.14/4.81    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 35.14/4.81  fof(f1384,plain,(
% 35.14/4.81    spl6_7 <=> r1_tarski(k2_zfmisc_1(sK0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,k2_zfmisc_1(sK0,sK1)))),
% 35.14/4.81    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 35.14/4.81  fof(f88565,plain,(
% 35.14/4.81    spl6_65 <=> k1_xboole_0 = sK1),
% 35.14/4.81    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).
% 35.14/4.81  fof(f88662,plain,(
% 35.14/4.81    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (spl6_7 | ~spl6_65)),
% 35.14/4.81    inference(forward_demodulation,[],[f88661,f57290])).
% 35.14/4.81  fof(f57290,plain,(
% 35.14/4.81    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 35.14/4.81    inference(forward_demodulation,[],[f57289,f33])).
% 35.14/4.81  fof(f33,plain,(
% 35.14/4.81    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 35.14/4.81    inference(cnf_transformation,[],[f10])).
% 35.14/4.81  fof(f10,axiom,(
% 35.14/4.81    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 35.14/4.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 35.14/4.81  fof(f57289,plain,(
% 35.14/4.81    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,k5_xboole_0(X1,X1))) )),
% 35.14/4.81    inference(forward_demodulation,[],[f57288,f35])).
% 35.14/4.81  fof(f35,plain,(
% 35.14/4.81    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 35.14/4.81    inference(cnf_transformation,[],[f16])).
% 35.14/4.81  fof(f16,plain,(
% 35.14/4.81    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 35.14/4.81    inference(rectify,[],[f2])).
% 35.14/4.81  fof(f2,axiom,(
% 35.14/4.81    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 35.14/4.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 35.14/4.81  fof(f57288,plain,(
% 35.14/4.81    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1)))) )),
% 35.14/4.81    inference(forward_demodulation,[],[f57172,f33])).
% 35.14/4.81  fof(f57172,plain,(
% 35.14/4.81    ( ! [X0,X1] : (k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1))) = k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1))) )),
% 35.14/4.81    inference(superposition,[],[f49,f35])).
% 35.14/4.81  fof(f49,plain,(
% 35.14/4.81    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 35.14/4.81    inference(definition_unfolding,[],[f45,f39,f39])).
% 35.14/4.81  fof(f39,plain,(
% 35.14/4.81    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 35.14/4.81    inference(cnf_transformation,[],[f6])).
% 35.14/4.81  fof(f6,axiom,(
% 35.14/4.81    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 35.14/4.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 35.14/4.81  fof(f45,plain,(
% 35.14/4.81    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 35.14/4.81    inference(cnf_transformation,[],[f13])).
% 35.14/4.81  fof(f13,axiom,(
% 35.14/4.81    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 35.14/4.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 35.14/4.81  fof(f88661,plain,(
% 35.14/4.81    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),k1_xboole_0) | (spl6_7 | ~spl6_65)),
% 35.14/4.81    inference(forward_demodulation,[],[f88660,f57290])).
% 35.14/4.81  fof(f88660,plain,(
% 35.14/4.81    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),k2_zfmisc_1(sK2,k1_xboole_0)) | (spl6_7 | ~spl6_65)),
% 35.14/4.81    inference(forward_demodulation,[],[f88606,f57290])).
% 35.14/4.81  fof(f88606,plain,(
% 35.14/4.81    ~r1_tarski(k2_zfmisc_1(sK0,k2_zfmisc_1(sK0,k1_xboole_0)),k2_zfmisc_1(sK2,k2_zfmisc_1(sK0,k1_xboole_0))) | (spl6_7 | ~spl6_65)),
% 35.14/4.81    inference(superposition,[],[f1386,f88567])).
% 35.14/4.81  fof(f88567,plain,(
% 35.14/4.81    k1_xboole_0 = sK1 | ~spl6_65),
% 35.14/4.81    inference(avatar_component_clause,[],[f88565])).
% 35.14/4.81  fof(f1386,plain,(
% 35.14/4.81    ~r1_tarski(k2_zfmisc_1(sK0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,k2_zfmisc_1(sK0,sK1))) | spl6_7),
% 35.14/4.81    inference(avatar_component_clause,[],[f1384])).
% 35.14/4.81  fof(f88568,plain,(
% 35.14/4.81    spl6_65 | spl6_2 | ~spl6_36),
% 35.14/4.81    inference(avatar_split_clause,[],[f88560,f83745,f58,f88565])).
% 35.14/4.81  fof(f58,plain,(
% 35.14/4.81    spl6_2 <=> r1_tarski(sK0,sK2)),
% 35.14/4.81    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 35.14/4.81  fof(f83745,plain,(
% 35.14/4.81    spl6_36 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),
% 35.14/4.81    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 35.14/4.81  fof(f88560,plain,(
% 35.14/4.81    k1_xboole_0 = sK1 | (spl6_2 | ~spl6_36)),
% 35.14/4.81    inference(unit_resulting_resolution,[],[f60,f83747,f46])).
% 35.14/4.81  fof(f46,plain,(
% 35.14/4.81    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 35.14/4.81    inference(cnf_transformation,[],[f23])).
% 35.14/4.81  fof(f23,plain,(
% 35.14/4.81    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 35.14/4.81    inference(ennf_transformation,[],[f11])).
% 35.14/4.81  fof(f11,axiom,(
% 35.14/4.81    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 35.14/4.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 35.14/4.81  fof(f83747,plain,(
% 35.14/4.81    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | ~spl6_36),
% 35.14/4.81    inference(avatar_component_clause,[],[f83745])).
% 35.14/4.81  fof(f60,plain,(
% 35.14/4.81    ~r1_tarski(sK0,sK2) | spl6_2),
% 35.14/4.81    inference(avatar_component_clause,[],[f58])).
% 35.14/4.81  fof(f84267,plain,(
% 35.14/4.81    spl6_43),
% 35.14/4.81    inference(avatar_contradiction_clause,[],[f84253])).
% 35.14/4.81  fof(f84253,plain,(
% 35.14/4.81    $false | spl6_43),
% 35.14/4.81    inference(unit_resulting_resolution,[],[f112,f84249])).
% 35.14/4.81  fof(f84249,plain,(
% 35.14/4.81    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl6_43),
% 35.14/4.81    inference(avatar_component_clause,[],[f84247])).
% 35.14/4.81  fof(f112,plain,(
% 35.14/4.81    ( ! [X7] : (r1_tarski(k1_xboole_0,X7)) )),
% 35.14/4.81    inference(superposition,[],[f36,f97])).
% 35.14/4.81  fof(f97,plain,(
% 35.14/4.81    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 35.14/4.81    inference(unit_resulting_resolution,[],[f89,f34])).
% 35.14/4.81  fof(f34,plain,(
% 35.14/4.81    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 35.14/4.81    inference(cnf_transformation,[],[f27])).
% 35.14/4.81  fof(f27,plain,(
% 35.14/4.81    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 35.14/4.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f26])).
% 35.14/4.81  fof(f26,plain,(
% 35.14/4.81    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 35.14/4.81    introduced(choice_axiom,[])).
% 35.14/4.81  fof(f20,plain,(
% 35.14/4.81    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 35.14/4.81    inference(ennf_transformation,[],[f4])).
% 35.14/4.81  fof(f4,axiom,(
% 35.14/4.81    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 35.14/4.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 35.14/4.81  fof(f89,plain,(
% 35.14/4.81    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 35.14/4.81    inference(unit_resulting_resolution,[],[f81,f41])).
% 35.14/4.81  fof(f41,plain,(
% 35.14/4.81    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 35.14/4.81    inference(cnf_transformation,[],[f29])).
% 35.14/4.81  fof(f29,plain,(
% 35.14/4.81    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 35.14/4.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f28])).
% 35.14/4.81  fof(f28,plain,(
% 35.14/4.81    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 35.14/4.81    introduced(choice_axiom,[])).
% 35.14/4.81  fof(f21,plain,(
% 35.14/4.81    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 35.14/4.81    inference(ennf_transformation,[],[f17])).
% 35.14/4.81  fof(f17,plain,(
% 35.14/4.81    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 35.14/4.81    inference(rectify,[],[f3])).
% 35.14/4.81  fof(f3,axiom,(
% 35.14/4.81    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 35.14/4.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 35.14/4.81  fof(f81,plain,(
% 35.14/4.81    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 35.14/4.81    inference(forward_demodulation,[],[f77,f33])).
% 35.14/4.81  fof(f77,plain,(
% 35.14/4.81    ( ! [X0] : (r1_xboole_0(X0,k5_xboole_0(X0,X0))) )),
% 35.14/4.81    inference(superposition,[],[f38,f35])).
% 35.14/4.81  fof(f38,plain,(
% 35.14/4.81    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 35.14/4.81    inference(cnf_transformation,[],[f5])).
% 35.14/4.81  fof(f5,axiom,(
% 35.14/4.81    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 35.14/4.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).
% 35.14/4.81  fof(f36,plain,(
% 35.14/4.81    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 35.14/4.81    inference(cnf_transformation,[],[f8])).
% 35.14/4.81  fof(f8,axiom,(
% 35.14/4.81    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 35.14/4.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 35.14/4.81  fof(f84250,plain,(
% 35.14/4.81    ~spl6_43 | spl6_1 | spl6_3 | ~spl6_37),
% 35.14/4.81    inference(avatar_split_clause,[],[f84241,f83753,f62,f52,f84247])).
% 35.14/4.81  fof(f52,plain,(
% 35.14/4.81    spl6_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 35.14/4.81    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 35.14/4.81  fof(f62,plain,(
% 35.14/4.81    spl6_3 <=> r1_tarski(sK1,sK3)),
% 35.14/4.81    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 35.14/4.81  fof(f83753,plain,(
% 35.14/4.81    spl6_37 <=> k1_xboole_0 = sK0),
% 35.14/4.81    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 35.14/4.81  fof(f84241,plain,(
% 35.14/4.81    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (spl6_1 | spl6_3 | ~spl6_37)),
% 35.14/4.81    inference(forward_demodulation,[],[f84240,f57290])).
% 35.14/4.81  fof(f84240,plain,(
% 35.14/4.81    ~r1_tarski(k2_zfmisc_1(sK1,k1_xboole_0),k1_xboole_0) | (spl6_1 | spl6_3 | ~spl6_37)),
% 35.14/4.81    inference(forward_demodulation,[],[f84239,f57290])).
% 35.14/4.81  fof(f84239,plain,(
% 35.14/4.81    ~r1_tarski(k2_zfmisc_1(sK1,k1_xboole_0),k2_zfmisc_1(sK3,k1_xboole_0)) | (spl6_1 | spl6_3 | ~spl6_37)),
% 35.14/4.81    inference(forward_demodulation,[],[f84238,f79607])).
% 35.14/4.81  fof(f79607,plain,(
% 35.14/4.81    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 35.14/4.81    inference(forward_demodulation,[],[f79606,f33])).
% 35.14/4.81  fof(f79606,plain,(
% 35.14/4.81    ( ! [X0,X1] : (k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 35.14/4.81    inference(forward_demodulation,[],[f79605,f33])).
% 35.14/4.81  fof(f79605,plain,(
% 35.14/4.81    ( ! [X0,X1] : (k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(k5_xboole_0(X0,X0),X1)) )),
% 35.14/4.81    inference(forward_demodulation,[],[f79604,f35])).
% 35.14/4.81  fof(f79604,plain,(
% 35.14/4.81    ( ! [X0,X1] : (k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X0)),X1)) )),
% 35.14/4.81    inference(forward_demodulation,[],[f79448,f35])).
% 35.14/4.81  fof(f79448,plain,(
% 35.14/4.81    ( ! [X0,X1] : (k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X0)),X1) = k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,k3_xboole_0(X1,X1)))) )),
% 35.14/4.81    inference(superposition,[],[f50,f27592])).
% 35.14/4.81  fof(f27592,plain,(
% 35.14/4.81    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2))) )),
% 35.14/4.81    inference(superposition,[],[f48,f35])).
% 35.14/4.81  fof(f48,plain,(
% 35.14/4.81    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 35.14/4.81    inference(cnf_transformation,[],[f12])).
% 35.14/4.81  fof(f12,axiom,(
% 35.14/4.81    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 35.14/4.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 35.14/4.81  fof(f50,plain,(
% 35.14/4.81    ( ! [X2,X0,X1] : (k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 35.14/4.81    inference(definition_unfolding,[],[f44,f39,f39])).
% 35.14/4.81  fof(f44,plain,(
% 35.14/4.81    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 35.14/4.81    inference(cnf_transformation,[],[f13])).
% 35.14/4.81  fof(f84238,plain,(
% 35.14/4.81    ~r1_tarski(k2_zfmisc_1(sK1,k2_zfmisc_1(k1_xboole_0,sK1)),k2_zfmisc_1(sK3,k2_zfmisc_1(k1_xboole_0,sK1))) | (spl6_1 | spl6_3 | ~spl6_37)),
% 35.14/4.81    inference(forward_demodulation,[],[f84237,f83755])).
% 35.14/4.81  fof(f83755,plain,(
% 35.14/4.81    k1_xboole_0 = sK0 | ~spl6_37),
% 35.14/4.81    inference(avatar_component_clause,[],[f83753])).
% 35.14/4.81  fof(f84237,plain,(
% 35.14/4.81    ~r1_tarski(k2_zfmisc_1(sK1,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK3,k2_zfmisc_1(sK0,sK1))) | (spl6_1 | spl6_3)),
% 35.14/4.81    inference(unit_resulting_resolution,[],[f54,f64,f46])).
% 35.14/4.81  fof(f64,plain,(
% 35.14/4.81    ~r1_tarski(sK1,sK3) | spl6_3),
% 35.14/4.81    inference(avatar_component_clause,[],[f62])).
% 35.14/4.81  fof(f54,plain,(
% 35.14/4.81    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | spl6_1),
% 35.14/4.81    inference(avatar_component_clause,[],[f52])).
% 35.14/4.81  fof(f83756,plain,(
% 35.14/4.81    spl6_37 | spl6_3 | ~spl6_35),
% 35.14/4.81    inference(avatar_split_clause,[],[f83750,f83740,f62,f83753])).
% 35.14/4.81  fof(f83740,plain,(
% 35.14/4.81    spl6_35 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))),
% 35.14/4.81    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 35.14/4.81  fof(f83750,plain,(
% 35.14/4.81    r1_tarski(sK1,sK3) | k1_xboole_0 = sK0 | ~spl6_35),
% 35.14/4.81    inference(resolution,[],[f83742,f47])).
% 35.14/4.81  fof(f47,plain,(
% 35.14/4.81    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 35.14/4.81    inference(cnf_transformation,[],[f23])).
% 35.14/4.81  fof(f83742,plain,(
% 35.14/4.81    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) | ~spl6_35),
% 35.14/4.81    inference(avatar_component_clause,[],[f83740])).
% 35.14/4.81  fof(f83748,plain,(
% 35.14/4.81    spl6_36 | ~spl6_15),
% 35.14/4.81    inference(avatar_split_clause,[],[f83712,f10054,f83745])).
% 35.14/4.81  fof(f10054,plain,(
% 35.14/4.81    spl6_15 <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),
% 35.14/4.81    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 35.14/4.81  fof(f83712,plain,(
% 35.14/4.81    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | ~spl6_15),
% 35.14/4.81    inference(superposition,[],[f80534,f10056])).
% 35.14/4.81  fof(f10056,plain,(
% 35.14/4.81    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)) | ~spl6_15),
% 35.14/4.81    inference(avatar_component_clause,[],[f10054])).
% 35.14/4.81  fof(f80534,plain,(
% 35.14/4.81    ( ! [X24,X23,X25,X22] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(X22,X23),k2_zfmisc_1(X25,X24)),k2_zfmisc_1(X22,X24))) )),
% 35.14/4.81    inference(forward_demodulation,[],[f80249,f48])).
% 35.14/4.81  fof(f80249,plain,(
% 35.14/4.81    ( ! [X24,X23,X25,X22] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X22,X25),k3_xboole_0(X23,X24)),k2_zfmisc_1(X22,X24))) )),
% 35.14/4.81    inference(superposition,[],[f75862,f27649])).
% 35.14/4.81  fof(f27649,plain,(
% 35.14/4.81    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0)) )),
% 35.14/4.81    inference(superposition,[],[f48,f35])).
% 35.14/4.81  fof(f75862,plain,(
% 35.14/4.81    ( ! [X6,X4,X5,X3] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(X4,k3_xboole_0(X5,X6)),X3),k2_zfmisc_1(X4,X6))) )),
% 35.14/4.81    inference(superposition,[],[f74822,f37])).
% 35.14/4.81  fof(f37,plain,(
% 35.14/4.81    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 35.14/4.81    inference(cnf_transformation,[],[f1])).
% 35.14/4.81  fof(f1,axiom,(
% 35.14/4.81    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 35.14/4.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 35.14/4.81  fof(f74822,plain,(
% 35.14/4.81    ( ! [X130,X128,X131,X129] : (r1_tarski(k3_xboole_0(X131,k2_zfmisc_1(X128,k3_xboole_0(X129,X130))),k2_zfmisc_1(X128,X130))) )),
% 35.14/4.81    inference(superposition,[],[f478,f27592])).
% 35.14/4.82  fof(f478,plain,(
% 35.14/4.82    ( ! [X23,X21,X22] : (r1_tarski(k3_xboole_0(X21,k3_xboole_0(X22,X23)),X23)) )),
% 35.14/4.82    inference(superposition,[],[f72,f43])).
% 35.14/4.82  fof(f43,plain,(
% 35.14/4.82    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 35.14/4.82    inference(cnf_transformation,[],[f7])).
% 35.14/4.82  fof(f7,axiom,(
% 35.14/4.82    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 35.14/4.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 35.14/4.82  fof(f72,plain,(
% 35.14/4.82    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 35.14/4.82    inference(superposition,[],[f36,f37])).
% 35.14/4.82  fof(f83743,plain,(
% 35.14/4.82    spl6_35 | ~spl6_6),
% 35.14/4.82    inference(avatar_split_clause,[],[f83711,f1379,f83740])).
% 35.14/4.82  fof(f1379,plain,(
% 35.14/4.82    spl6_6 <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 35.14/4.82    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 35.14/4.82  fof(f83711,plain,(
% 35.14/4.82    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) | ~spl6_6),
% 35.14/4.82    inference(superposition,[],[f80534,f1381])).
% 35.14/4.82  fof(f1381,plain,(
% 35.14/4.82    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl6_6),
% 35.14/4.82    inference(avatar_component_clause,[],[f1379])).
% 35.14/4.82  fof(f10057,plain,(
% 35.14/4.82    spl6_15 | ~spl6_6),
% 35.14/4.82    inference(avatar_split_clause,[],[f1399,f1379,f10054])).
% 35.14/4.82  fof(f1399,plain,(
% 35.14/4.82    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)) | ~spl6_6),
% 35.14/4.82    inference(superposition,[],[f186,f1381])).
% 35.14/4.82  fof(f186,plain,(
% 35.14/4.82    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4))) )),
% 35.14/4.82    inference(superposition,[],[f139,f37])).
% 35.14/4.82  fof(f139,plain,(
% 35.14/4.82    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X1)) )),
% 35.14/4.82    inference(unit_resulting_resolution,[],[f72,f42])).
% 35.14/4.82  fof(f42,plain,(
% 35.14/4.82    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 35.14/4.82    inference(cnf_transformation,[],[f22])).
% 35.14/4.82  fof(f22,plain,(
% 35.14/4.82    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 35.14/4.82    inference(ennf_transformation,[],[f9])).
% 35.14/4.82  fof(f9,axiom,(
% 35.14/4.82    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 35.14/4.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 35.14/4.82  fof(f1387,plain,(
% 35.14/4.82    ~spl6_7 | spl6_1 | spl6_2),
% 35.14/4.82    inference(avatar_split_clause,[],[f1223,f58,f52,f1384])).
% 35.14/4.82  fof(f1223,plain,(
% 35.14/4.82    ~r1_tarski(k2_zfmisc_1(sK0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,k2_zfmisc_1(sK0,sK1))) | (spl6_1 | spl6_2)),
% 35.14/4.82    inference(unit_resulting_resolution,[],[f60,f54,f46])).
% 35.14/4.82  fof(f1382,plain,(
% 35.14/4.82    spl6_6 | ~spl6_4),
% 35.14/4.82    inference(avatar_split_clause,[],[f138,f67,f1379])).
% 35.14/4.82  fof(f67,plain,(
% 35.14/4.82    spl6_4 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 35.14/4.82    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 35.14/4.82  fof(f138,plain,(
% 35.14/4.82    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl6_4),
% 35.14/4.82    inference(unit_resulting_resolution,[],[f69,f42])).
% 35.14/4.82  fof(f69,plain,(
% 35.14/4.82    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl6_4),
% 35.14/4.82    inference(avatar_component_clause,[],[f67])).
% 35.14/4.82  fof(f70,plain,(
% 35.14/4.82    spl6_4),
% 35.14/4.82    inference(avatar_split_clause,[],[f30,f67])).
% 35.14/4.82  fof(f30,plain,(
% 35.14/4.82    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 35.14/4.82    inference(cnf_transformation,[],[f25])).
% 35.14/4.82  fof(f25,plain,(
% 35.14/4.82    (~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 35.14/4.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f24])).
% 35.14/4.82  fof(f24,plain,(
% 35.14/4.82    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),
% 35.14/4.82    introduced(choice_axiom,[])).
% 35.14/4.82  fof(f19,plain,(
% 35.14/4.82    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 35.14/4.82    inference(flattening,[],[f18])).
% 35.14/4.82  fof(f18,plain,(
% 35.14/4.82    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 35.14/4.82    inference(ennf_transformation,[],[f15])).
% 35.14/4.82  fof(f15,negated_conjecture,(
% 35.14/4.82    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 35.14/4.82    inference(negated_conjecture,[],[f14])).
% 35.14/4.82  fof(f14,conjecture,(
% 35.14/4.82    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 35.14/4.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 35.14/4.82  fof(f65,plain,(
% 35.14/4.82    ~spl6_2 | ~spl6_3),
% 35.14/4.82    inference(avatar_split_clause,[],[f32,f62,f58])).
% 35.14/4.82  fof(f32,plain,(
% 35.14/4.82    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 35.14/4.82    inference(cnf_transformation,[],[f25])).
% 35.14/4.82  fof(f55,plain,(
% 35.14/4.82    ~spl6_1),
% 35.14/4.82    inference(avatar_split_clause,[],[f31,f52])).
% 35.14/4.82  fof(f31,plain,(
% 35.14/4.82    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 35.14/4.82    inference(cnf_transformation,[],[f25])).
% 35.14/4.82  % SZS output end Proof for theBenchmark
% 35.14/4.82  % (1693)------------------------------
% 35.14/4.82  % (1693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 35.14/4.82  % (1693)Termination reason: Refutation
% 35.14/4.82  
% 35.14/4.82  % (1693)Memory used [KB]: 131127
% 35.14/4.82  % (1693)Time elapsed: 4.388 s
% 35.14/4.82  % (1693)------------------------------
% 35.14/4.82  % (1693)------------------------------
% 35.14/4.82  % (1674)Success in time 4.469 s
%------------------------------------------------------------------------------
