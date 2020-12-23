%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:12 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 488 expanded)
%              Number of leaves         :   26 ( 139 expanded)
%              Depth                    :   20
%              Number of atoms          :  581 (2344 expanded)
%              Number of equality atoms :  338 (2000 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2975,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f293,f567,f657,f751,f795,f828,f847,f866,f2018,f2046,f2847,f2901,f2947,f2974])).

fof(f2974,plain,
    ( ~ spl8_2
    | spl8_5
    | spl8_25
    | ~ spl8_40 ),
    inference(avatar_contradiction_clause,[],[f2973])).

fof(f2973,plain,
    ( $false
    | ~ spl8_2
    | spl8_5
    | spl8_25
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f2921,f123])).

fof(f123,plain,
    ( ~ r1_tarski(sK0,sK4)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl8_5
  <=> r1_tarski(sK0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f2921,plain,
    ( r1_tarski(sK0,sK4)
    | ~ spl8_2
    | spl8_25
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f2920,f75])).

fof(f75,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2920,plain,
    ( ~ r1_tarski(sK1,sK1)
    | r1_tarski(sK0,sK4)
    | ~ spl8_2
    | spl8_25
    | ~ spl8_40 ),
    inference(forward_demodulation,[],[f2563,f89])).

fof(f89,plain,
    ( sK1 = sK5
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl8_2
  <=> sK1 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f2563,plain,
    ( r1_tarski(sK0,sK4)
    | ~ r1_tarski(sK5,sK1)
    | spl8_25
    | ~ spl8_40 ),
    inference(resolution,[],[f1437,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f1437,plain,
    ( ! [X5] :
        ( ~ r1_tarski(k2_zfmisc_1(X5,sK5),k2_zfmisc_1(sK0,sK1))
        | r1_tarski(X5,sK4) )
    | spl8_25
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f1401,f505])).

fof(f505,plain,
    ( k1_xboole_0 != sK5
    | spl8_25 ),
    inference(avatar_component_clause,[],[f504])).

fof(f504,plain,
    ( spl8_25
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f1401,plain,
    ( ! [X5] :
        ( ~ r1_tarski(k2_zfmisc_1(X5,sK5),k2_zfmisc_1(sK0,sK1))
        | r1_tarski(X5,sK4)
        | k1_xboole_0 = sK5 )
    | ~ spl8_40 ),
    inference(superposition,[],[f48,f1376])).

fof(f1376,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5)
    | ~ spl8_40 ),
    inference(equality_resolution,[],[f865])).

fof(f865,plain,
    ( ! [X2,X0,X1] :
        ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
        | k2_zfmisc_1(sK4,sK5) = X0 )
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f864])).

fof(f864,plain,
    ( spl8_40
  <=> ! [X1,X0,X2] :
        ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
        | k2_zfmisc_1(sK4,sK5) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f2947,plain,
    ( ~ spl8_2
    | spl8_6
    | ~ spl8_40 ),
    inference(avatar_contradiction_clause,[],[f2946])).

fof(f2946,plain,
    ( $false
    | ~ spl8_2
    | spl8_6
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f2945,f75])).

fof(f2945,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ spl8_2
    | spl8_6
    | ~ spl8_40 ),
    inference(forward_demodulation,[],[f2553,f89])).

fof(f2553,plain,
    ( ~ r1_tarski(sK1,sK5)
    | spl8_6
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f2552,f34])).

fof(f34,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f15,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_mcart_1)).

fof(f2552,plain,
    ( ~ r1_tarski(sK1,sK5)
    | k1_xboole_0 = sK1
    | spl8_6
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f2548,f127])).

fof(f127,plain,
    ( ~ r1_tarski(sK4,sK0)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl8_6
  <=> r1_tarski(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f2548,plain,
    ( ~ r1_tarski(sK1,sK5)
    | r1_tarski(sK4,sK0)
    | k1_xboole_0 = sK1
    | ~ spl8_40 ),
    inference(resolution,[],[f1399,f48])).

fof(f1399,plain,
    ( ! [X3] :
        ( r1_tarski(k2_zfmisc_1(sK4,X3),k2_zfmisc_1(sK0,sK1))
        | ~ r1_tarski(X3,sK5) )
    | ~ spl8_40 ),
    inference(superposition,[],[f47,f1376])).

fof(f2901,plain,
    ( ~ spl8_6
    | ~ spl8_5
    | spl8_1 ),
    inference(avatar_split_clause,[],[f2899,f84,f121,f125])).

fof(f84,plain,
    ( spl8_1
  <=> sK0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f2899,plain,
    ( ~ r1_tarski(sK0,sK4)
    | ~ r1_tarski(sK4,sK0)
    | spl8_1 ),
    inference(extensionality_resolution,[],[f41,f86])).

fof(f86,plain,
    ( sK0 != sK4
    | spl8_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2847,plain,
    ( spl8_2
    | spl8_9
    | spl8_25
    | spl8_26
    | ~ spl8_40 ),
    inference(avatar_contradiction_clause,[],[f2846])).

fof(f2846,plain,
    ( $false
    | spl8_2
    | spl8_9
    | spl8_25
    | spl8_26
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f2754,f38])).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f2754,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl8_2
    | spl8_9
    | spl8_25
    | spl8_26
    | ~ spl8_40 ),
    inference(backward_demodulation,[],[f952,f2692])).

fof(f2692,plain,
    ( ! [X0] : k1_xboole_0 = X0
    | spl8_2
    | spl8_25
    | spl8_26
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f2688,f90])).

fof(f90,plain,
    ( sK1 != sK5
    | spl8_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f2688,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | sK1 = sK5 )
    | spl8_25
    | spl8_26
    | ~ spl8_40 ),
    inference(equality_resolution,[],[f1445])).

fof(f1445,plain,
    ( ! [X24,X23,X25,X22] :
        ( k2_zfmisc_1(k2_zfmisc_1(X23,X24),X25) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X22)
        | k1_xboole_0 = X22
        | sK5 = X24 )
    | spl8_25
    | spl8_26
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f1444,f509])).

fof(f509,plain,
    ( k1_xboole_0 != sK4
    | spl8_26 ),
    inference(avatar_component_clause,[],[f508])).

fof(f508,plain,
    ( spl8_26
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f1444,plain,
    ( ! [X24,X23,X25,X22] :
        ( k2_zfmisc_1(k2_zfmisc_1(X23,X24),X25) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X22)
        | k1_xboole_0 = X22
        | k1_xboole_0 = sK4
        | sK5 = X24 )
    | spl8_25
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f1409,f505])).

fof(f1409,plain,
    ( ! [X24,X23,X25,X22] :
        ( k2_zfmisc_1(k2_zfmisc_1(X23,X24),X25) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X22)
        | k1_xboole_0 = X22
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK4
        | sK5 = X24 )
    | ~ spl8_40 ),
    inference(superposition,[],[f70,f1376])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X1 = X4 ) ),
    inference(definition_unfolding,[],[f58,f45,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).

fof(f952,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
    | spl8_9 ),
    inference(resolution,[],[f424,f141])).

fof(f141,plain,(
    ! [X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X3,X2),k1_xboole_0)
      | ~ r1_tarski(X3,k1_xboole_0) ) ),
    inference(superposition,[],[f46,f78])).

fof(f78,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f424,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k1_xboole_0)
    | spl8_9 ),
    inference(resolution,[],[f400,f141])).

fof(f400,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k1_xboole_0)
    | spl8_9 ),
    inference(subsumption_resolution,[],[f398,f38])).

fof(f398,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | spl8_9 ),
    inference(extensionality_resolution,[],[f41,f209])).

fof(f209,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | spl8_9 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl8_9
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f2046,plain,
    ( spl8_3
    | ~ spl8_39 ),
    inference(avatar_contradiction_clause,[],[f2045])).

fof(f2045,plain,
    ( $false
    | spl8_3
    | ~ spl8_39 ),
    inference(subsumption_resolution,[],[f1159,f94])).

fof(f94,plain,
    ( sK2 != sK6
    | spl8_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl8_3
  <=> sK2 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f1159,plain,
    ( sK2 = sK6
    | ~ spl8_39 ),
    inference(equality_resolution,[],[f846])).

fof(f846,plain,
    ( ! [X2,X0,X1] :
        ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
        | sK6 = X1 )
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f845])).

fof(f845,plain,
    ( spl8_39
  <=> ! [X1,X0,X2] :
        ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
        | sK6 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f2018,plain,
    ( spl8_4
    | ~ spl8_38 ),
    inference(avatar_contradiction_clause,[],[f2017])).

fof(f2017,plain,
    ( $false
    | spl8_4
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f98,f1063])).

fof(f1063,plain,
    ( sK3 = sK7
    | ~ spl8_38 ),
    inference(equality_resolution,[],[f827])).

fof(f827,plain,
    ( ! [X2,X0,X1] :
        ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
        | sK7 = X2 )
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f826])).

fof(f826,plain,
    ( spl8_38
  <=> ! [X1,X0,X2] :
        ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
        | sK7 = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f98,plain,
    ( sK3 != sK7
    | spl8_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl8_4
  <=> sK3 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f866,plain,
    ( spl8_9
    | spl8_40 ),
    inference(avatar_split_clause,[],[f855,f864,f207])).

fof(f855,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
      | k2_zfmisc_1(sK4,sK5) = X0 ) ),
    inference(superposition,[],[f74,f63])).

fof(f63,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    inference(definition_unfolding,[],[f32,f50,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_mcart_1)).

fof(f32,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | X0 = X3 ) ),
    inference(definition_unfolding,[],[f60,f45,f45,f45])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

fof(f847,plain,
    ( spl8_9
    | spl8_39 ),
    inference(avatar_split_clause,[],[f836,f845,f207])).

fof(f836,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
      | sK6 = X1 ) ),
    inference(superposition,[],[f73,f63])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | X1 = X4 ) ),
    inference(definition_unfolding,[],[f61,f45,f45,f45])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f828,plain,
    ( spl8_9
    | spl8_38 ),
    inference(avatar_split_clause,[],[f817,f826,f207])).

fof(f817,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
      | sK7 = X2 ) ),
    inference(superposition,[],[f72,f63])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | X2 = X5 ) ),
    inference(definition_unfolding,[],[f62,f45,f45,f45])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f795,plain,
    ( spl8_8
    | ~ spl8_9
    | spl8_7 ),
    inference(avatar_split_clause,[],[f794,f199,f207,f203])).

fof(f203,plain,
    ( spl8_8
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f199,plain,
    ( spl8_7
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f794,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | spl8_7 ),
    inference(subsumption_resolution,[],[f773,f200])).

fof(f200,plain,
    ( k1_xboole_0 != sK7
    | spl8_7 ),
    inference(avatar_component_clause,[],[f199])).

fof(f773,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | k1_xboole_0 = sK7 ),
    inference(superposition,[],[f42,f63])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f751,plain,(
    ~ spl8_26 ),
    inference(avatar_contradiction_clause,[],[f750])).

fof(f750,plain,
    ( $false
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f749,f33])).

fof(f33,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f25])).

fof(f749,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f748,f34])).

fof(f748,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f747,f35])).

fof(f35,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f25])).

fof(f747,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f742,f36])).

fof(f36,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f25])).

fof(f742,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl8_26 ),
    inference(trivial_inequality_removal,[],[f726])).

fof(f726,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl8_26 ),
    inference(superposition,[],[f68,f714])).

fof(f714,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl8_26 ),
    inference(forward_demodulation,[],[f713,f78])).

fof(f713,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k1_xboole_0,sK7)
    | ~ spl8_26 ),
    inference(forward_demodulation,[],[f712,f78])).

fof(f712,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK6),sK7)
    | ~ spl8_26 ),
    inference(forward_demodulation,[],[f709,f78])).

fof(f709,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5),sK6),sK7)
    | ~ spl8_26 ),
    inference(backward_demodulation,[],[f63,f510])).

fof(f510,plain,
    ( k1_xboole_0 = sK4
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f508])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f52,f50])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f657,plain,
    ( spl8_8
    | ~ spl8_25 ),
    inference(avatar_contradiction_clause,[],[f656])).

fof(f656,plain,
    ( $false
    | spl8_8
    | ~ spl8_25 ),
    inference(subsumption_resolution,[],[f655,f78])).

fof(f655,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK6)
    | spl8_8
    | ~ spl8_25 ),
    inference(forward_demodulation,[],[f654,f77])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f654,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0),sK6)
    | spl8_8
    | ~ spl8_25 ),
    inference(forward_demodulation,[],[f204,f506])).

fof(f506,plain,
    ( k1_xboole_0 = sK5
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f504])).

fof(f204,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f203])).

fof(f567,plain,(
    ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f566])).

fof(f566,plain,
    ( $false
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f565,f33])).

fof(f565,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f564,f34])).

fof(f564,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f563,f35])).

fof(f563,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f554,f36])).

fof(f554,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl8_8 ),
    inference(trivial_inequality_removal,[],[f538])).

fof(f538,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl8_8 ),
    inference(superposition,[],[f68,f345])).

fof(f345,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f331,f78])).

fof(f331,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k1_xboole_0,sK7)
    | ~ spl8_8 ),
    inference(backward_demodulation,[],[f63,f205])).

fof(f205,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f203])).

fof(f293,plain,(
    ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f292])).

fof(f292,plain,
    ( $false
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f291,f34])).

fof(f291,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f290,f33])).

fof(f290,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl8_7 ),
    inference(trivial_inequality_removal,[],[f281])).

fof(f281,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl8_7 ),
    inference(superposition,[],[f42,f276])).

fof(f276,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f275,f35])).

fof(f275,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | ~ spl8_7 ),
    inference(trivial_inequality_removal,[],[f266])).

fof(f266,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | ~ spl8_7 ),
    inference(superposition,[],[f42,f261])).

fof(f261,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f260,f36])).

fof(f260,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK3
    | ~ spl8_7 ),
    inference(trivial_inequality_removal,[],[f251])).

fof(f251,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK3
    | ~ spl8_7 ),
    inference(superposition,[],[f42,f248])).

fof(f248,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl8_7 ),
    inference(forward_demodulation,[],[f245,f77])).

fof(f245,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k1_xboole_0)
    | ~ spl8_7 ),
    inference(backward_demodulation,[],[f63,f201])).

fof(f201,plain,
    ( k1_xboole_0 = sK7
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f199])).

fof(f99,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f37,f96,f92,f88,f84])).

fof(f37,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:40:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.45  % (31124)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.47  % (31133)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.47  % (31146)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.48  % (31138)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.19/0.48  % (31138)Refutation not found, incomplete strategy% (31138)------------------------------
% 0.19/0.48  % (31138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (31146)Refutation not found, incomplete strategy% (31146)------------------------------
% 0.19/0.49  % (31146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (31138)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (31138)Memory used [KB]: 1663
% 0.19/0.49  % (31138)Time elapsed: 0.098 s
% 0.19/0.49  % (31138)------------------------------
% 0.19/0.49  % (31138)------------------------------
% 0.19/0.49  % (31146)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (31146)Memory used [KB]: 6268
% 0.19/0.49  % (31146)Time elapsed: 0.106 s
% 0.19/0.49  % (31146)------------------------------
% 0.19/0.49  % (31146)------------------------------
% 0.19/0.49  % (31126)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.50  % (31142)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.50  % (31135)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.50  % (31121)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.51  % (31120)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.51  % (31122)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.51  % (31125)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.52  % (31144)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.19/0.52  % (31148)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.52  % (31140)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.52  % (31128)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.52  % (31147)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.52  % (31145)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.19/0.53  % (31127)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.53  % (31121)Refutation not found, incomplete strategy% (31121)------------------------------
% 0.19/0.53  % (31121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (31121)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (31121)Memory used [KB]: 1791
% 0.19/0.53  % (31121)Time elapsed: 0.107 s
% 0.19/0.53  % (31121)------------------------------
% 0.19/0.53  % (31121)------------------------------
% 0.19/0.53  % (31143)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.53  % (31137)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.19/0.53  % (31139)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.53  % (31136)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.19/0.53  % (31129)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.53  % (31149)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.53  % (31149)Refutation not found, incomplete strategy% (31149)------------------------------
% 0.19/0.53  % (31149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (31149)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (31149)Memory used [KB]: 1663
% 0.19/0.53  % (31149)Time elapsed: 0.138 s
% 0.19/0.53  % (31149)------------------------------
% 0.19/0.53  % (31149)------------------------------
% 0.19/0.54  % (31130)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.54  % (31123)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.54  % (31134)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.54  % (31131)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.54  % (31136)Refutation not found, incomplete strategy% (31136)------------------------------
% 0.19/0.54  % (31136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (31136)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (31136)Memory used [KB]: 10618
% 0.19/0.54  % (31136)Time elapsed: 0.109 s
% 0.19/0.54  % (31136)------------------------------
% 0.19/0.54  % (31136)------------------------------
% 0.19/0.54  % (31134)Refutation not found, incomplete strategy% (31134)------------------------------
% 0.19/0.54  % (31134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (31134)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (31134)Memory used [KB]: 1663
% 0.19/0.54  % (31134)Time elapsed: 0.140 s
% 0.19/0.54  % (31134)------------------------------
% 0.19/0.54  % (31134)------------------------------
% 0.19/0.56  % (31141)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.19/0.57  % (31132)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.57  % (31132)Refutation not found, incomplete strategy% (31132)------------------------------
% 0.19/0.57  % (31132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.57  % (31132)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.57  
% 0.19/0.57  % (31132)Memory used [KB]: 10618
% 0.19/0.57  % (31132)Time elapsed: 0.144 s
% 0.19/0.57  % (31132)------------------------------
% 0.19/0.57  % (31132)------------------------------
% 0.19/0.66  % (31126)Refutation found. Thanks to Tanya!
% 0.19/0.66  % SZS status Theorem for theBenchmark
% 0.19/0.66  % SZS output start Proof for theBenchmark
% 0.19/0.66  fof(f2975,plain,(
% 0.19/0.66    $false),
% 0.19/0.66    inference(avatar_sat_refutation,[],[f99,f293,f567,f657,f751,f795,f828,f847,f866,f2018,f2046,f2847,f2901,f2947,f2974])).
% 0.19/0.66  fof(f2974,plain,(
% 0.19/0.66    ~spl8_2 | spl8_5 | spl8_25 | ~spl8_40),
% 0.19/0.66    inference(avatar_contradiction_clause,[],[f2973])).
% 0.19/0.66  fof(f2973,plain,(
% 0.19/0.66    $false | (~spl8_2 | spl8_5 | spl8_25 | ~spl8_40)),
% 0.19/0.66    inference(subsumption_resolution,[],[f2921,f123])).
% 0.19/0.66  fof(f123,plain,(
% 0.19/0.66    ~r1_tarski(sK0,sK4) | spl8_5),
% 0.19/0.66    inference(avatar_component_clause,[],[f121])).
% 0.19/0.66  fof(f121,plain,(
% 0.19/0.66    spl8_5 <=> r1_tarski(sK0,sK4)),
% 0.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.19/0.66  fof(f2921,plain,(
% 0.19/0.66    r1_tarski(sK0,sK4) | (~spl8_2 | spl8_25 | ~spl8_40)),
% 0.19/0.66    inference(subsumption_resolution,[],[f2920,f75])).
% 0.19/0.66  fof(f75,plain,(
% 0.19/0.66    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.66    inference(equality_resolution,[],[f40])).
% 0.19/0.66  fof(f40,plain,(
% 0.19/0.66    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.66    inference(cnf_transformation,[],[f27])).
% 0.19/0.66  fof(f27,plain,(
% 0.19/0.66    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.66    inference(flattening,[],[f26])).
% 0.19/0.66  fof(f26,plain,(
% 0.19/0.66    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.66    inference(nnf_transformation,[],[f1])).
% 0.19/0.66  fof(f1,axiom,(
% 0.19/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.66  fof(f2920,plain,(
% 0.19/0.66    ~r1_tarski(sK1,sK1) | r1_tarski(sK0,sK4) | (~spl8_2 | spl8_25 | ~spl8_40)),
% 0.19/0.66    inference(forward_demodulation,[],[f2563,f89])).
% 0.19/0.66  fof(f89,plain,(
% 0.19/0.66    sK1 = sK5 | ~spl8_2),
% 0.19/0.66    inference(avatar_component_clause,[],[f88])).
% 0.19/0.66  fof(f88,plain,(
% 0.19/0.66    spl8_2 <=> sK1 = sK5),
% 0.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.19/0.66  fof(f2563,plain,(
% 0.19/0.66    r1_tarski(sK0,sK4) | ~r1_tarski(sK5,sK1) | (spl8_25 | ~spl8_40)),
% 0.19/0.66    inference(resolution,[],[f1437,f47])).
% 0.19/0.66  fof(f47,plain,(
% 0.19/0.66    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.66    inference(cnf_transformation,[],[f16])).
% 0.19/0.66  fof(f16,plain,(
% 0.19/0.66    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 0.19/0.66    inference(ennf_transformation,[],[f5])).
% 0.19/0.66  fof(f5,axiom,(
% 0.19/0.66    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 0.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 0.19/0.66  fof(f1437,plain,(
% 0.19/0.66    ( ! [X5] : (~r1_tarski(k2_zfmisc_1(X5,sK5),k2_zfmisc_1(sK0,sK1)) | r1_tarski(X5,sK4)) ) | (spl8_25 | ~spl8_40)),
% 0.19/0.66    inference(subsumption_resolution,[],[f1401,f505])).
% 0.19/0.66  fof(f505,plain,(
% 0.19/0.66    k1_xboole_0 != sK5 | spl8_25),
% 0.19/0.66    inference(avatar_component_clause,[],[f504])).
% 0.19/0.66  fof(f504,plain,(
% 0.19/0.66    spl8_25 <=> k1_xboole_0 = sK5),
% 0.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.19/0.66  fof(f1401,plain,(
% 0.19/0.66    ( ! [X5] : (~r1_tarski(k2_zfmisc_1(X5,sK5),k2_zfmisc_1(sK0,sK1)) | r1_tarski(X5,sK4) | k1_xboole_0 = sK5) ) | ~spl8_40),
% 0.19/0.66    inference(superposition,[],[f48,f1376])).
% 0.19/0.66  fof(f1376,plain,(
% 0.19/0.66    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) | ~spl8_40),
% 0.19/0.66    inference(equality_resolution,[],[f865])).
% 0.19/0.66  fof(f865,plain,(
% 0.19/0.66    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k2_zfmisc_1(sK4,sK5) = X0) ) | ~spl8_40),
% 0.19/0.66    inference(avatar_component_clause,[],[f864])).
% 0.19/0.66  fof(f864,plain,(
% 0.19/0.66    spl8_40 <=> ! [X1,X0,X2] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k2_zfmisc_1(sK4,sK5) = X0)),
% 0.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).
% 0.19/0.66  fof(f48,plain,(
% 0.19/0.66    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 0.19/0.66    inference(cnf_transformation,[],[f17])).
% 0.19/0.66  fof(f17,plain,(
% 0.19/0.66    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 0.19/0.66    inference(ennf_transformation,[],[f4])).
% 0.19/0.66  fof(f4,axiom,(
% 0.19/0.66    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 0.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 0.19/0.66  fof(f2947,plain,(
% 0.19/0.66    ~spl8_2 | spl8_6 | ~spl8_40),
% 0.19/0.66    inference(avatar_contradiction_clause,[],[f2946])).
% 0.19/0.66  fof(f2946,plain,(
% 0.19/0.66    $false | (~spl8_2 | spl8_6 | ~spl8_40)),
% 0.19/0.66    inference(subsumption_resolution,[],[f2945,f75])).
% 0.19/0.66  fof(f2945,plain,(
% 0.19/0.66    ~r1_tarski(sK1,sK1) | (~spl8_2 | spl8_6 | ~spl8_40)),
% 0.19/0.66    inference(forward_demodulation,[],[f2553,f89])).
% 0.19/0.66  fof(f2553,plain,(
% 0.19/0.66    ~r1_tarski(sK1,sK5) | (spl8_6 | ~spl8_40)),
% 0.19/0.66    inference(subsumption_resolution,[],[f2552,f34])).
% 0.19/0.66  fof(f34,plain,(
% 0.19/0.66    k1_xboole_0 != sK1),
% 0.19/0.66    inference(cnf_transformation,[],[f25])).
% 0.19/0.66  fof(f25,plain,(
% 0.19/0.66    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 0.19/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f15,f24])).
% 0.19/0.66  fof(f24,plain,(
% 0.19/0.66    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.19/0.66    introduced(choice_axiom,[])).
% 0.19/0.66  fof(f15,plain,(
% 0.19/0.66    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 0.19/0.66    inference(flattening,[],[f14])).
% 0.19/0.66  fof(f14,plain,(
% 0.19/0.66    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 0.19/0.66    inference(ennf_transformation,[],[f13])).
% 0.19/0.66  fof(f13,negated_conjecture,(
% 0.19/0.66    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.66    inference(negated_conjecture,[],[f12])).
% 0.19/0.66  fof(f12,conjecture,(
% 0.19/0.66    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_mcart_1)).
% 0.19/0.66  fof(f2552,plain,(
% 0.19/0.66    ~r1_tarski(sK1,sK5) | k1_xboole_0 = sK1 | (spl8_6 | ~spl8_40)),
% 0.19/0.66    inference(subsumption_resolution,[],[f2548,f127])).
% 0.19/0.66  fof(f127,plain,(
% 0.19/0.66    ~r1_tarski(sK4,sK0) | spl8_6),
% 0.19/0.66    inference(avatar_component_clause,[],[f125])).
% 0.19/0.66  fof(f125,plain,(
% 0.19/0.66    spl8_6 <=> r1_tarski(sK4,sK0)),
% 0.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.19/0.66  fof(f2548,plain,(
% 0.19/0.66    ~r1_tarski(sK1,sK5) | r1_tarski(sK4,sK0) | k1_xboole_0 = sK1 | ~spl8_40),
% 0.19/0.66    inference(resolution,[],[f1399,f48])).
% 0.19/0.66  fof(f1399,plain,(
% 0.19/0.66    ( ! [X3] : (r1_tarski(k2_zfmisc_1(sK4,X3),k2_zfmisc_1(sK0,sK1)) | ~r1_tarski(X3,sK5)) ) | ~spl8_40),
% 0.19/0.66    inference(superposition,[],[f47,f1376])).
% 0.19/0.66  fof(f2901,plain,(
% 0.19/0.66    ~spl8_6 | ~spl8_5 | spl8_1),
% 0.19/0.66    inference(avatar_split_clause,[],[f2899,f84,f121,f125])).
% 0.19/0.66  fof(f84,plain,(
% 0.19/0.66    spl8_1 <=> sK0 = sK4),
% 0.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.19/0.66  fof(f2899,plain,(
% 0.19/0.66    ~r1_tarski(sK0,sK4) | ~r1_tarski(sK4,sK0) | spl8_1),
% 0.19/0.66    inference(extensionality_resolution,[],[f41,f86])).
% 0.19/0.66  fof(f86,plain,(
% 0.19/0.66    sK0 != sK4 | spl8_1),
% 0.19/0.66    inference(avatar_component_clause,[],[f84])).
% 0.19/0.66  fof(f41,plain,(
% 0.19/0.66    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.19/0.66    inference(cnf_transformation,[],[f27])).
% 0.19/0.66  fof(f2847,plain,(
% 0.19/0.66    spl8_2 | spl8_9 | spl8_25 | spl8_26 | ~spl8_40),
% 0.19/0.66    inference(avatar_contradiction_clause,[],[f2846])).
% 0.19/0.66  fof(f2846,plain,(
% 0.19/0.66    $false | (spl8_2 | spl8_9 | spl8_25 | spl8_26 | ~spl8_40)),
% 0.19/0.66    inference(subsumption_resolution,[],[f2754,f38])).
% 0.19/0.66  fof(f38,plain,(
% 0.19/0.66    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.19/0.66    inference(cnf_transformation,[],[f2])).
% 0.19/0.66  fof(f2,axiom,(
% 0.19/0.66    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.19/0.66  fof(f2754,plain,(
% 0.19/0.66    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (spl8_2 | spl8_9 | spl8_25 | spl8_26 | ~spl8_40)),
% 0.19/0.66    inference(backward_demodulation,[],[f952,f2692])).
% 0.19/0.66  fof(f2692,plain,(
% 0.19/0.66    ( ! [X0] : (k1_xboole_0 = X0) ) | (spl8_2 | spl8_25 | spl8_26 | ~spl8_40)),
% 0.19/0.66    inference(subsumption_resolution,[],[f2688,f90])).
% 0.19/0.66  fof(f90,plain,(
% 0.19/0.66    sK1 != sK5 | spl8_2),
% 0.19/0.66    inference(avatar_component_clause,[],[f88])).
% 0.19/0.66  fof(f2688,plain,(
% 0.19/0.66    ( ! [X0] : (k1_xboole_0 = X0 | sK1 = sK5) ) | (spl8_25 | spl8_26 | ~spl8_40)),
% 0.19/0.66    inference(equality_resolution,[],[f1445])).
% 0.19/0.66  fof(f1445,plain,(
% 0.19/0.66    ( ! [X24,X23,X25,X22] : (k2_zfmisc_1(k2_zfmisc_1(X23,X24),X25) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X22) | k1_xboole_0 = X22 | sK5 = X24) ) | (spl8_25 | spl8_26 | ~spl8_40)),
% 0.19/0.66    inference(subsumption_resolution,[],[f1444,f509])).
% 0.19/0.66  fof(f509,plain,(
% 0.19/0.66    k1_xboole_0 != sK4 | spl8_26),
% 0.19/0.66    inference(avatar_component_clause,[],[f508])).
% 0.19/0.66  fof(f508,plain,(
% 0.19/0.66    spl8_26 <=> k1_xboole_0 = sK4),
% 0.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.19/0.66  fof(f1444,plain,(
% 0.19/0.66    ( ! [X24,X23,X25,X22] : (k2_zfmisc_1(k2_zfmisc_1(X23,X24),X25) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X22) | k1_xboole_0 = X22 | k1_xboole_0 = sK4 | sK5 = X24) ) | (spl8_25 | ~spl8_40)),
% 0.19/0.66    inference(subsumption_resolution,[],[f1409,f505])).
% 0.19/0.66  fof(f1409,plain,(
% 0.19/0.66    ( ! [X24,X23,X25,X22] : (k2_zfmisc_1(k2_zfmisc_1(X23,X24),X25) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X22) | k1_xboole_0 = X22 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | sK5 = X24) ) | ~spl8_40),
% 0.19/0.66    inference(superposition,[],[f70,f1376])).
% 0.19/0.66  fof(f70,plain,(
% 0.19/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X1 = X4) )),
% 0.19/0.66    inference(definition_unfolding,[],[f58,f45,f45])).
% 0.19/0.66  fof(f45,plain,(
% 0.19/0.66    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.19/0.66    inference(cnf_transformation,[],[f7])).
% 0.19/0.66  fof(f7,axiom,(
% 0.19/0.66    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.19/0.66  fof(f58,plain,(
% 0.19/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (X1 = X4 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 0.19/0.66    inference(cnf_transformation,[],[f21])).
% 0.19/0.66  fof(f21,plain,(
% 0.19/0.66    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.19/0.66    inference(flattening,[],[f20])).
% 0.19/0.66  fof(f20,plain,(
% 0.19/0.66    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.19/0.66    inference(ennf_transformation,[],[f8])).
% 0.19/0.66  fof(f8,axiom,(
% 0.19/0.66    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).
% 0.19/0.66  fof(f952,plain,(
% 0.19/0.66    ~r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) | spl8_9),
% 0.19/0.66    inference(resolution,[],[f424,f141])).
% 0.19/0.66  fof(f141,plain,(
% 0.19/0.66    ( ! [X2,X3] : (r1_tarski(k2_zfmisc_1(X3,X2),k1_xboole_0) | ~r1_tarski(X3,k1_xboole_0)) )),
% 0.19/0.66    inference(superposition,[],[f46,f78])).
% 0.19/0.66  fof(f78,plain,(
% 0.19/0.66    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.19/0.66    inference(equality_resolution,[],[f43])).
% 0.19/0.66  fof(f43,plain,(
% 0.19/0.66    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.19/0.66    inference(cnf_transformation,[],[f29])).
% 0.19/0.66  fof(f29,plain,(
% 0.19/0.66    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.66    inference(flattening,[],[f28])).
% 0.19/0.66  fof(f28,plain,(
% 0.19/0.66    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.66    inference(nnf_transformation,[],[f3])).
% 0.19/0.66  fof(f3,axiom,(
% 0.19/0.66    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.66  fof(f46,plain,(
% 0.19/0.66    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.66    inference(cnf_transformation,[],[f16])).
% 0.19/0.66  fof(f424,plain,(
% 0.19/0.66    ~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k1_xboole_0) | spl8_9),
% 0.19/0.66    inference(resolution,[],[f400,f141])).
% 0.19/0.66  fof(f400,plain,(
% 0.19/0.66    ~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k1_xboole_0) | spl8_9),
% 0.19/0.66    inference(subsumption_resolution,[],[f398,f38])).
% 0.19/0.66  fof(f398,plain,(
% 0.19/0.66    ~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k1_xboole_0) | ~r1_tarski(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | spl8_9),
% 0.19/0.66    inference(extensionality_resolution,[],[f41,f209])).
% 0.19/0.66  fof(f209,plain,(
% 0.19/0.66    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | spl8_9),
% 0.19/0.66    inference(avatar_component_clause,[],[f207])).
% 0.19/0.66  fof(f207,plain,(
% 0.19/0.66    spl8_9 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 0.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.19/0.66  fof(f2046,plain,(
% 0.19/0.66    spl8_3 | ~spl8_39),
% 0.19/0.66    inference(avatar_contradiction_clause,[],[f2045])).
% 0.19/0.66  fof(f2045,plain,(
% 0.19/0.66    $false | (spl8_3 | ~spl8_39)),
% 0.19/0.66    inference(subsumption_resolution,[],[f1159,f94])).
% 0.19/0.66  fof(f94,plain,(
% 0.19/0.66    sK2 != sK6 | spl8_3),
% 0.19/0.66    inference(avatar_component_clause,[],[f92])).
% 0.19/0.66  fof(f92,plain,(
% 0.19/0.66    spl8_3 <=> sK2 = sK6),
% 0.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.19/0.66  fof(f1159,plain,(
% 0.19/0.66    sK2 = sK6 | ~spl8_39),
% 0.19/0.66    inference(equality_resolution,[],[f846])).
% 0.19/0.66  fof(f846,plain,(
% 0.19/0.66    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | sK6 = X1) ) | ~spl8_39),
% 0.19/0.66    inference(avatar_component_clause,[],[f845])).
% 0.19/0.66  fof(f845,plain,(
% 0.19/0.66    spl8_39 <=> ! [X1,X0,X2] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | sK6 = X1)),
% 0.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 0.19/0.66  fof(f2018,plain,(
% 0.19/0.66    spl8_4 | ~spl8_38),
% 0.19/0.66    inference(avatar_contradiction_clause,[],[f2017])).
% 0.19/0.66  fof(f2017,plain,(
% 0.19/0.66    $false | (spl8_4 | ~spl8_38)),
% 0.19/0.66    inference(subsumption_resolution,[],[f98,f1063])).
% 0.19/0.66  fof(f1063,plain,(
% 0.19/0.66    sK3 = sK7 | ~spl8_38),
% 0.19/0.66    inference(equality_resolution,[],[f827])).
% 0.19/0.66  fof(f827,plain,(
% 0.19/0.66    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | sK7 = X2) ) | ~spl8_38),
% 0.19/0.66    inference(avatar_component_clause,[],[f826])).
% 0.19/0.66  fof(f826,plain,(
% 0.19/0.66    spl8_38 <=> ! [X1,X0,X2] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | sK7 = X2)),
% 0.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 0.19/0.66  fof(f98,plain,(
% 0.19/0.66    sK3 != sK7 | spl8_4),
% 0.19/0.66    inference(avatar_component_clause,[],[f96])).
% 0.19/0.66  fof(f96,plain,(
% 0.19/0.66    spl8_4 <=> sK3 = sK7),
% 0.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.19/0.66  fof(f866,plain,(
% 0.19/0.66    spl8_9 | spl8_40),
% 0.19/0.66    inference(avatar_split_clause,[],[f855,f864,f207])).
% 0.19/0.66  fof(f855,plain,(
% 0.19/0.66    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k2_zfmisc_1(sK4,sK5) = X0) )),
% 0.19/0.66    inference(superposition,[],[f74,f63])).
% 0.19/0.66  fof(f63,plain,(
% 0.19/0.66    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)),
% 0.19/0.66    inference(definition_unfolding,[],[f32,f50,f50])).
% 0.19/0.66  fof(f50,plain,(
% 0.19/0.66    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.19/0.66    inference(cnf_transformation,[],[f10])).
% 0.19/0.66  fof(f10,axiom,(
% 0.19/0.66    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)),
% 0.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_mcart_1)).
% 0.19/0.66  fof(f32,plain,(
% 0.19/0.66    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 0.19/0.66    inference(cnf_transformation,[],[f25])).
% 0.19/0.66  fof(f74,plain,(
% 0.19/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | X0 = X3) )),
% 0.19/0.66    inference(definition_unfolding,[],[f60,f45,f45,f45])).
% 0.19/0.66  fof(f60,plain,(
% 0.19/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (X0 = X3 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 0.19/0.66    inference(cnf_transformation,[],[f23])).
% 0.19/0.66  fof(f23,plain,(
% 0.19/0.66    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.19/0.66    inference(flattening,[],[f22])).
% 0.19/0.66  fof(f22,plain,(
% 0.19/0.66    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.19/0.66    inference(ennf_transformation,[],[f9])).
% 0.19/0.66  fof(f9,axiom,(
% 0.19/0.66    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)))),
% 0.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).
% 0.19/0.66  fof(f847,plain,(
% 0.19/0.66    spl8_9 | spl8_39),
% 0.19/0.66    inference(avatar_split_clause,[],[f836,f845,f207])).
% 0.19/0.66  fof(f836,plain,(
% 0.19/0.66    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | sK6 = X1) )),
% 0.19/0.66    inference(superposition,[],[f73,f63])).
% 0.19/0.66  fof(f73,plain,(
% 0.19/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | X1 = X4) )),
% 0.19/0.66    inference(definition_unfolding,[],[f61,f45,f45,f45])).
% 0.19/0.66  fof(f61,plain,(
% 0.19/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (X1 = X4 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 0.19/0.66    inference(cnf_transformation,[],[f23])).
% 0.19/0.66  fof(f828,plain,(
% 0.19/0.66    spl8_9 | spl8_38),
% 0.19/0.66    inference(avatar_split_clause,[],[f817,f826,f207])).
% 0.19/0.66  fof(f817,plain,(
% 0.19/0.66    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | sK7 = X2) )),
% 0.19/0.66    inference(superposition,[],[f72,f63])).
% 0.19/0.66  fof(f72,plain,(
% 0.19/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | X2 = X5) )),
% 0.19/0.66    inference(definition_unfolding,[],[f62,f45,f45,f45])).
% 0.19/0.66  fof(f62,plain,(
% 0.19/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (X2 = X5 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 0.19/0.66    inference(cnf_transformation,[],[f23])).
% 0.19/0.66  fof(f795,plain,(
% 0.19/0.66    spl8_8 | ~spl8_9 | spl8_7),
% 0.19/0.66    inference(avatar_split_clause,[],[f794,f199,f207,f203])).
% 0.19/0.66  fof(f203,plain,(
% 0.19/0.66    spl8_8 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)),
% 0.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.19/0.66  fof(f199,plain,(
% 0.19/0.66    spl8_7 <=> k1_xboole_0 = sK7),
% 0.19/0.66    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.19/0.66  fof(f794,plain,(
% 0.19/0.66    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | spl8_7),
% 0.19/0.66    inference(subsumption_resolution,[],[f773,f200])).
% 0.19/0.66  fof(f200,plain,(
% 0.19/0.66    k1_xboole_0 != sK7 | spl8_7),
% 0.19/0.66    inference(avatar_component_clause,[],[f199])).
% 0.19/0.66  fof(f773,plain,(
% 0.19/0.66    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | k1_xboole_0 = sK7),
% 0.19/0.66    inference(superposition,[],[f42,f63])).
% 0.19/0.66  fof(f42,plain,(
% 0.19/0.66    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.19/0.66    inference(cnf_transformation,[],[f29])).
% 0.19/0.66  fof(f751,plain,(
% 0.19/0.66    ~spl8_26),
% 0.19/0.66    inference(avatar_contradiction_clause,[],[f750])).
% 0.19/0.66  fof(f750,plain,(
% 0.19/0.66    $false | ~spl8_26),
% 0.19/0.66    inference(subsumption_resolution,[],[f749,f33])).
% 0.19/0.66  fof(f33,plain,(
% 0.19/0.66    k1_xboole_0 != sK0),
% 0.19/0.66    inference(cnf_transformation,[],[f25])).
% 0.19/0.66  fof(f749,plain,(
% 0.19/0.66    k1_xboole_0 = sK0 | ~spl8_26),
% 0.19/0.66    inference(subsumption_resolution,[],[f748,f34])).
% 0.19/0.66  fof(f748,plain,(
% 0.19/0.66    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl8_26),
% 0.19/0.66    inference(subsumption_resolution,[],[f747,f35])).
% 0.19/0.66  fof(f35,plain,(
% 0.19/0.66    k1_xboole_0 != sK2),
% 0.19/0.66    inference(cnf_transformation,[],[f25])).
% 0.19/0.66  fof(f747,plain,(
% 0.19/0.66    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl8_26),
% 0.19/0.66    inference(subsumption_resolution,[],[f742,f36])).
% 0.19/0.66  fof(f36,plain,(
% 0.19/0.66    k1_xboole_0 != sK3),
% 0.19/0.66    inference(cnf_transformation,[],[f25])).
% 0.19/0.66  fof(f742,plain,(
% 0.19/0.66    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl8_26),
% 0.19/0.66    inference(trivial_inequality_removal,[],[f726])).
% 0.19/0.66  fof(f726,plain,(
% 0.19/0.66    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl8_26),
% 0.19/0.66    inference(superposition,[],[f68,f714])).
% 0.19/0.66  fof(f714,plain,(
% 0.19/0.66    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | ~spl8_26),
% 0.19/0.66    inference(forward_demodulation,[],[f713,f78])).
% 0.19/0.66  fof(f713,plain,(
% 0.19/0.66    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k1_xboole_0,sK7) | ~spl8_26),
% 0.19/0.66    inference(forward_demodulation,[],[f712,f78])).
% 0.19/0.66  fof(f712,plain,(
% 0.19/0.66    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK6),sK7) | ~spl8_26),
% 0.19/0.66    inference(forward_demodulation,[],[f709,f78])).
% 0.19/0.66  fof(f709,plain,(
% 0.19/0.66    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5),sK6),sK7) | ~spl8_26),
% 0.19/0.66    inference(backward_demodulation,[],[f63,f510])).
% 0.19/0.66  fof(f510,plain,(
% 0.19/0.66    k1_xboole_0 = sK4 | ~spl8_26),
% 0.19/0.66    inference(avatar_component_clause,[],[f508])).
% 0.19/0.66  fof(f68,plain,(
% 0.19/0.66    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.19/0.66    inference(definition_unfolding,[],[f52,f50])).
% 0.19/0.66  fof(f52,plain,(
% 0.19/0.66    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.19/0.66    inference(cnf_transformation,[],[f31])).
% 0.19/0.66  fof(f31,plain,(
% 0.19/0.66    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.66    inference(flattening,[],[f30])).
% 0.19/0.66  fof(f30,plain,(
% 0.19/0.66    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.19/0.66    inference(nnf_transformation,[],[f11])).
% 0.19/0.66  fof(f11,axiom,(
% 0.19/0.66    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 0.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).
% 0.19/0.66  fof(f657,plain,(
% 0.19/0.66    spl8_8 | ~spl8_25),
% 0.19/0.66    inference(avatar_contradiction_clause,[],[f656])).
% 0.19/0.66  fof(f656,plain,(
% 0.19/0.66    $false | (spl8_8 | ~spl8_25)),
% 0.19/0.66    inference(subsumption_resolution,[],[f655,f78])).
% 0.19/0.66  fof(f655,plain,(
% 0.19/0.66    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK6) | (spl8_8 | ~spl8_25)),
% 0.19/0.66    inference(forward_demodulation,[],[f654,f77])).
% 0.19/0.66  fof(f77,plain,(
% 0.19/0.66    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.19/0.66    inference(equality_resolution,[],[f44])).
% 0.19/0.66  fof(f44,plain,(
% 0.19/0.66    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.19/0.66    inference(cnf_transformation,[],[f29])).
% 0.19/0.66  fof(f654,plain,(
% 0.19/0.66    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0),sK6) | (spl8_8 | ~spl8_25)),
% 0.19/0.66    inference(forward_demodulation,[],[f204,f506])).
% 0.19/0.66  fof(f506,plain,(
% 0.19/0.66    k1_xboole_0 = sK5 | ~spl8_25),
% 0.19/0.66    inference(avatar_component_clause,[],[f504])).
% 0.19/0.66  fof(f204,plain,(
% 0.19/0.66    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | spl8_8),
% 0.19/0.66    inference(avatar_component_clause,[],[f203])).
% 0.19/0.66  fof(f567,plain,(
% 0.19/0.66    ~spl8_8),
% 0.19/0.66    inference(avatar_contradiction_clause,[],[f566])).
% 0.19/0.66  fof(f566,plain,(
% 0.19/0.66    $false | ~spl8_8),
% 0.19/0.66    inference(subsumption_resolution,[],[f565,f33])).
% 0.19/0.66  fof(f565,plain,(
% 0.19/0.66    k1_xboole_0 = sK0 | ~spl8_8),
% 0.19/0.66    inference(subsumption_resolution,[],[f564,f34])).
% 0.19/0.66  fof(f564,plain,(
% 0.19/0.66    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl8_8),
% 0.19/0.66    inference(subsumption_resolution,[],[f563,f35])).
% 0.19/0.66  fof(f563,plain,(
% 0.19/0.66    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl8_8),
% 0.19/0.66    inference(subsumption_resolution,[],[f554,f36])).
% 0.19/0.66  fof(f554,plain,(
% 0.19/0.66    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl8_8),
% 0.19/0.66    inference(trivial_inequality_removal,[],[f538])).
% 0.19/0.66  fof(f538,plain,(
% 0.19/0.66    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl8_8),
% 0.19/0.66    inference(superposition,[],[f68,f345])).
% 0.19/0.66  fof(f345,plain,(
% 0.19/0.66    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | ~spl8_8),
% 0.19/0.66    inference(forward_demodulation,[],[f331,f78])).
% 0.19/0.66  fof(f331,plain,(
% 0.19/0.66    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k1_xboole_0,sK7) | ~spl8_8),
% 0.19/0.66    inference(backward_demodulation,[],[f63,f205])).
% 0.19/0.66  fof(f205,plain,(
% 0.19/0.66    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | ~spl8_8),
% 0.19/0.66    inference(avatar_component_clause,[],[f203])).
% 0.19/0.66  fof(f293,plain,(
% 0.19/0.66    ~spl8_7),
% 0.19/0.66    inference(avatar_contradiction_clause,[],[f292])).
% 0.19/0.66  fof(f292,plain,(
% 0.19/0.66    $false | ~spl8_7),
% 0.19/0.66    inference(subsumption_resolution,[],[f291,f34])).
% 0.19/0.66  fof(f291,plain,(
% 0.19/0.66    k1_xboole_0 = sK1 | ~spl8_7),
% 0.19/0.66    inference(subsumption_resolution,[],[f290,f33])).
% 0.19/0.66  fof(f290,plain,(
% 0.19/0.66    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl8_7),
% 0.19/0.66    inference(trivial_inequality_removal,[],[f281])).
% 0.19/0.66  fof(f281,plain,(
% 0.19/0.66    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl8_7),
% 0.19/0.66    inference(superposition,[],[f42,f276])).
% 0.19/0.66  fof(f276,plain,(
% 0.19/0.66    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_7),
% 0.19/0.66    inference(subsumption_resolution,[],[f275,f35])).
% 0.19/0.66  fof(f275,plain,(
% 0.19/0.66    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | ~spl8_7),
% 0.19/0.66    inference(trivial_inequality_removal,[],[f266])).
% 0.19/0.66  fof(f266,plain,(
% 0.19/0.66    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | ~spl8_7),
% 0.19/0.66    inference(superposition,[],[f42,f261])).
% 0.19/0.66  fof(f261,plain,(
% 0.19/0.66    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl8_7),
% 0.19/0.66    inference(subsumption_resolution,[],[f260,f36])).
% 0.19/0.66  fof(f260,plain,(
% 0.19/0.66    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | k1_xboole_0 = sK3 | ~spl8_7),
% 0.19/0.66    inference(trivial_inequality_removal,[],[f251])).
% 0.19/0.66  fof(f251,plain,(
% 0.19/0.66    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | k1_xboole_0 = sK3 | ~spl8_7),
% 0.19/0.66    inference(superposition,[],[f42,f248])).
% 0.19/0.66  fof(f248,plain,(
% 0.19/0.66    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | ~spl8_7),
% 0.19/0.66    inference(forward_demodulation,[],[f245,f77])).
% 0.19/0.66  fof(f245,plain,(
% 0.19/0.66    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k1_xboole_0) | ~spl8_7),
% 0.19/0.66    inference(backward_demodulation,[],[f63,f201])).
% 0.19/0.66  fof(f201,plain,(
% 0.19/0.66    k1_xboole_0 = sK7 | ~spl8_7),
% 0.19/0.66    inference(avatar_component_clause,[],[f199])).
% 0.19/0.66  fof(f99,plain,(
% 0.19/0.66    ~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4),
% 0.19/0.66    inference(avatar_split_clause,[],[f37,f96,f92,f88,f84])).
% 0.19/0.66  fof(f37,plain,(
% 0.19/0.66    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 0.19/0.66    inference(cnf_transformation,[],[f25])).
% 0.19/0.66  % SZS output end Proof for theBenchmark
% 0.19/0.66  % (31126)------------------------------
% 0.19/0.66  % (31126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.66  % (31126)Termination reason: Refutation
% 0.19/0.66  
% 0.19/0.66  % (31126)Memory used [KB]: 11769
% 0.19/0.66  % (31126)Time elapsed: 0.260 s
% 0.19/0.66  % (31126)------------------------------
% 0.19/0.66  % (31126)------------------------------
% 0.19/0.67  % (31118)Success in time 0.314 s
%------------------------------------------------------------------------------
