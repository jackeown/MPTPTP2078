%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0426+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:29 EST 2020

% Result     : Theorem 10.06s
% Output     : Refutation 10.06s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 224 expanded)
%              Number of leaves         :   28 (  72 expanded)
%              Depth                    :   14
%              Number of atoms          :  458 (1030 expanded)
%              Number of equality atoms :   68 (  91 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10798,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1017,f1034,f1040,f2480,f2482,f2511,f2991,f3387,f10775])).

fof(f10775,plain,
    ( spl29_1
    | ~ spl29_4
    | ~ spl29_10
    | ~ spl29_11 ),
    inference(avatar_contradiction_clause,[],[f10774])).

fof(f10774,plain,
    ( $false
    | spl29_1
    | ~ spl29_4
    | ~ spl29_10
    | ~ spl29_11 ),
    inference(subsumption_resolution,[],[f10773,f846])).

fof(f846,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f407])).

fof(f407,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f10773,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_tarski(sK9(k1_xboole_0)),k1_xboole_0)
    | spl29_1
    | ~ spl29_4
    | ~ spl29_10
    | ~ spl29_11 ),
    inference(forward_demodulation,[],[f4670,f6590])).

fof(f6590,plain,
    ( k1_xboole_0 = sK6
    | spl29_1
    | ~ spl29_4
    | ~ spl29_11 ),
    inference(resolution,[],[f5686,f906])).

fof(f906,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f774])).

fof(f774,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( sP3(X1,X0)
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f697])).

fof(f697,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( sP3(X1,X0)
        | k1_xboole_0 = X0 ) ) ),
    inference(definition_folding,[],[f689,f696,f695])).

% (16085)ins+10_1_av=off:fde=none:gsp=input_only:irw=on:igbrr=0.7:igpr=on:igrr=16/1:igrp=400:igrpq=2.0:igs=1003:igwr=on:lcm=predicate:lma=on:nm=64:newcnf=on:nwc=3:sp=occurrence:uhcvi=on_62 on theBenchmark
fof(f695,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ! [X3] :
              ( r2_hidden(X2,X3)
              | ~ r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f696,plain,(
    ! [X1,X0] :
      ( ( k1_setfam_1(X0) = X1
      <=> sP2(X0,X1) )
      | ~ sP3(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f689,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f547])).

fof(f547,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f5686,plain,
    ( ~ sP3(k1_setfam_1(sK6),sK6)
    | spl29_1
    | ~ spl29_4
    | ~ spl29_11 ),
    inference(resolution,[],[f4536,f928])).

fof(f928,plain,(
    ! [X1] :
      ( sP2(X1,k1_setfam_1(X1))
      | ~ sP3(k1_setfam_1(X1),X1) ) ),
    inference(equality_resolution,[],[f898])).

fof(f898,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | k1_setfam_1(X1) != X0
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f767])).

fof(f767,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X1) = X0
          | ~ sP2(X1,X0) )
        & ( sP2(X1,X0)
          | k1_setfam_1(X1) != X0 ) )
      | ~ sP3(X0,X1) ) ),
    inference(rectify,[],[f766])).

fof(f766,plain,(
    ! [X1,X0] :
      ( ( ( k1_setfam_1(X0) = X1
          | ~ sP2(X0,X1) )
        & ( sP2(X0,X1)
          | k1_setfam_1(X0) != X1 ) )
      | ~ sP3(X1,X0) ) ),
    inference(nnf_transformation,[],[f696])).

fof(f4536,plain,
    ( ~ sP2(sK6,k1_setfam_1(sK6))
    | spl29_1
    | ~ spl29_4
    | ~ spl29_11 ),
    inference(subsumption_resolution,[],[f4531,f3392])).

fof(f3392,plain,
    ( ! [X13] :
        ( ~ r2_hidden(sK5,sK28(X13,sK5))
        | ~ sP2(X13,k1_setfam_1(sK6)) )
    | spl29_1
    | ~ spl29_11 ),
    inference(forward_demodulation,[],[f1030,f2510])).

fof(f2510,plain,
    ( k8_setfam_1(sK4,sK6) = k1_setfam_1(sK6)
    | ~ spl29_11 ),
    inference(avatar_component_clause,[],[f2509])).

fof(f2509,plain,
    ( spl29_11
  <=> k8_setfam_1(sK4,sK6) = k1_setfam_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_11])])).

fof(f1030,plain,
    ( ! [X13] :
        ( ~ r2_hidden(sK5,sK28(X13,sK5))
        | ~ sP2(X13,k8_setfam_1(sK4,sK6)) )
    | spl29_1 ),
    inference(resolution,[],[f1013,f902])).

fof(f902,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X5,sK28(X0,X5))
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f773])).

fof(f773,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ( ( ( ~ r2_hidden(sK26(X0,X1),sK27(X0,X1))
              & r2_hidden(sK27(X0,X1),X0) )
            | ~ r2_hidden(sK26(X0,X1),X1) )
          & ( ! [X4] :
                ( r2_hidden(sK26(X0,X1),X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(sK26(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ( ~ r2_hidden(X5,sK28(X0,X5))
                & r2_hidden(sK28(X0,X5),X0) ) )
            & ( ! [X7] :
                  ( r2_hidden(X5,X7)
                  | ~ r2_hidden(X7,X0) )
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP2(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK26,sK27,sK28])],[f769,f772,f771,f770])).

fof(f770,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK26(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK26(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK26(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK26(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f771,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(sK26(X0,X1),X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(sK26(X0,X1),sK27(X0,X1))
        & r2_hidden(sK27(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f772,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK28(X0,X5))
        & r2_hidden(sK28(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f769,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2] :
            ( ( ? [X3] :
                  ( ~ r2_hidden(X2,X3)
                  & r2_hidden(X3,X0) )
              | ~ r2_hidden(X2,X1) )
            & ( ! [X4] :
                  ( r2_hidden(X2,X4)
                  | ~ r2_hidden(X4,X0) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ? [X6] :
                  ( ~ r2_hidden(X5,X6)
                  & r2_hidden(X6,X0) ) )
            & ( ! [X7] :
                  ( r2_hidden(X5,X7)
                  | ~ r2_hidden(X7,X0) )
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP2(X0,X1) ) ) ),
    inference(rectify,[],[f768])).

fof(f768,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2] :
            ( ( ? [X3] :
                  ( ~ r2_hidden(X2,X3)
                  & r2_hidden(X3,X0) )
              | ~ r2_hidden(X2,X1) )
            & ( ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ? [X3] :
                  ( ~ r2_hidden(X2,X3)
                  & r2_hidden(X3,X0) ) )
            & ( ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f695])).

fof(f1013,plain,
    ( ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6))
    | spl29_1 ),
    inference(avatar_component_clause,[],[f1012])).

fof(f1012,plain,
    ( spl29_1
  <=> r2_hidden(sK5,k8_setfam_1(sK4,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_1])])).

fof(f4531,plain,
    ( ~ sP2(sK6,k1_setfam_1(sK6))
    | r2_hidden(sK5,sK28(sK6,sK5))
    | spl29_1
    | ~ spl29_4
    | ~ spl29_11 ),
    inference(resolution,[],[f3394,f1039])).

fof(f1039,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK6)
        | r2_hidden(sK5,X4) )
    | ~ spl29_4 ),
    inference(avatar_component_clause,[],[f1038])).

fof(f1038,plain,
    ( spl29_4
  <=> ! [X4] :
        ( r2_hidden(sK5,X4)
        | ~ r2_hidden(X4,sK6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_4])])).

fof(f3394,plain,
    ( ! [X12] :
        ( r2_hidden(sK28(X12,sK5),X12)
        | ~ sP2(X12,k1_setfam_1(sK6)) )
    | spl29_1
    | ~ spl29_11 ),
    inference(forward_demodulation,[],[f1029,f2510])).

fof(f1029,plain,
    ( ! [X12] :
        ( r2_hidden(sK28(X12,sK5),X12)
        | ~ sP2(X12,k8_setfam_1(sK4,sK6)) )
    | spl29_1 ),
    inference(resolution,[],[f1013,f901])).

fof(f901,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(sK28(X0,X5),X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f773])).

fof(f4670,plain,
    ( sK6 = k2_xboole_0(k1_tarski(sK9(sK6)),sK6)
    | ~ spl29_10 ),
    inference(resolution,[],[f2486,f889])).

fof(f889,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f677])).

fof(f677,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f304])).

fof(f304,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f2486,plain,
    ( r2_hidden(sK9(sK6),sK6)
    | ~ spl29_10 ),
    inference(resolution,[],[f2479,f791])).

fof(f791,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f711])).

fof(f711,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK9(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK9(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f627,f710])).

fof(f710,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK9(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK9(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f627,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f433])).

fof(f433,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f2479,plain,
    ( r2_hidden(sK20(k1_zfmisc_1(sK4),sK6),sK6)
    | ~ spl29_10 ),
    inference(avatar_component_clause,[],[f2478])).

fof(f2478,plain,
    ( spl29_10
  <=> r2_hidden(sK20(k1_zfmisc_1(sK4),sK6),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_10])])).

fof(f3387,plain,
    ( ~ spl29_1
    | ~ spl29_2
    | spl29_3
    | ~ spl29_11 ),
    inference(avatar_contradiction_clause,[],[f3386])).

fof(f3386,plain,
    ( $false
    | ~ spl29_1
    | ~ spl29_2
    | spl29_3
    | ~ spl29_11 ),
    inference(subsumption_resolution,[],[f3385,f1765])).

fof(f1765,plain,
    ( ~ r2_hidden(sK5,k1_setfam_1(sK6))
    | ~ spl29_2
    | spl29_3 ),
    inference(resolution,[],[f1069,f1060])).

fof(f1060,plain,
    ( r1_tarski(k1_setfam_1(sK6),sK7)
    | ~ spl29_2 ),
    inference(resolution,[],[f1016,f897])).

fof(f897,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f688])).

fof(f688,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f605])).

fof(f605,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f1016,plain,
    ( r2_hidden(sK7,sK6)
    | ~ spl29_2 ),
    inference(avatar_component_clause,[],[f1015])).

fof(f1015,plain,
    ( spl29_2
  <=> r2_hidden(sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_2])])).

fof(f1069,plain,
    ( ! [X9] :
        ( ~ r1_tarski(X9,sK7)
        | ~ r2_hidden(sK5,X9) )
    | spl29_3 ),
    inference(resolution,[],[f1033,f868])).

fof(f868,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f755])).

fof(f755,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK23(X0,X1),X1)
          & r2_hidden(sK23(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23])],[f753,f754])).

fof(f754,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK23(X0,X1),X1)
        & r2_hidden(sK23(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f753,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f752])).

fof(f752,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f670])).

fof(f670,plain,(
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

fof(f1033,plain,
    ( ~ r2_hidden(sK5,sK7)
    | spl29_3 ),
    inference(avatar_component_clause,[],[f1032])).

fof(f1032,plain,
    ( spl29_3
  <=> r2_hidden(sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_3])])).

fof(f3385,plain,
    ( r2_hidden(sK5,k1_setfam_1(sK6))
    | ~ spl29_1
    | ~ spl29_11 ),
    inference(forward_demodulation,[],[f1036,f2510])).

fof(f1036,plain,
    ( r2_hidden(sK5,k8_setfam_1(sK4,sK6))
    | ~ spl29_1 ),
    inference(avatar_component_clause,[],[f1012])).

fof(f2991,plain,
    ( spl29_1
    | ~ spl29_9 ),
    inference(avatar_contradiction_clause,[],[f2990])).

fof(f2990,plain,
    ( $false
    | spl29_1
    | ~ spl29_9 ),
    inference(subsumption_resolution,[],[f2989,f850])).

fof(f850,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f2989,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK4)))
    | spl29_1
    | ~ spl29_9 ),
    inference(subsumption_resolution,[],[f2986,f776])).

fof(f776,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f703])).

fof(f703,plain,
    ( ( ( ~ r2_hidden(sK5,sK7)
        & r2_hidden(sK7,sK6) )
      | ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6)) )
    & ( ! [X4] :
          ( r2_hidden(sK5,X4)
          | ~ r2_hidden(X4,sK6) )
      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) )
    & r2_hidden(sK5,sK4)
    & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f700,f702,f701])).

fof(f701,plain,
    ( ? [X0,X1,X2] :
        ( ( ? [X3] :
              ( ~ r2_hidden(X1,X3)
              & r2_hidden(X3,X2) )
          | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
        & ( ! [X4] :
              ( r2_hidden(X1,X4)
              | ~ r2_hidden(X4,X2) )
          | r2_hidden(X1,k8_setfam_1(X0,X2)) )
        & r2_hidden(X1,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ( ? [X3] :
            ( ~ r2_hidden(sK5,X3)
            & r2_hidden(X3,sK6) )
        | ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6)) )
      & ( ! [X4] :
            ( r2_hidden(sK5,X4)
            | ~ r2_hidden(X4,sK6) )
        | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) )
      & r2_hidden(sK5,sK4)
      & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f702,plain,
    ( ? [X3] :
        ( ~ r2_hidden(sK5,X3)
        & r2_hidden(X3,sK6) )
   => ( ~ r2_hidden(sK5,sK7)
      & r2_hidden(sK7,sK6) ) ),
    introduced(choice_axiom,[])).

fof(f700,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3] :
            ( ~ r2_hidden(X1,X3)
            & r2_hidden(X3,X2) )
        | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & ( ! [X4] :
            ( r2_hidden(X1,X4)
            | ~ r2_hidden(X4,X2) )
        | r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f699])).

fof(f699,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3] :
            ( ~ r2_hidden(X1,X3)
            & r2_hidden(X3,X2) )
        | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & ( ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) )
        | r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f698])).

fof(f698,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3] :
            ( ~ r2_hidden(X1,X3)
            & r2_hidden(X3,X2) )
        | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & ( ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) )
        | r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f624])).

fof(f624,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f623])).

fof(f623,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f615])).

fof(f615,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( r2_hidden(X1,X0)
         => ( r2_hidden(X1,k8_setfam_1(X0,X2))
          <=> ! [X3] :
                ( r2_hidden(X3,X2)
               => r2_hidden(X1,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f614])).

fof(f614,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( r2_hidden(X1,X0)
       => ( r2_hidden(X1,k8_setfam_1(X0,X2))
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_setfam_1)).

fof(f2986,plain,
    ( ~ r2_hidden(sK5,sK4)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK4)))
    | spl29_1
    | ~ spl29_9 ),
    inference(superposition,[],[f2947,f915])).

fof(f915,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f781])).

fof(f781,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f625])).

fof(f625,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f546])).

fof(f546,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f2947,plain,
    ( ~ r2_hidden(sK5,k8_setfam_1(sK4,k1_xboole_0))
    | spl29_1
    | ~ spl29_9 ),
    inference(forward_demodulation,[],[f1013,f2476])).

fof(f2476,plain,
    ( k1_xboole_0 = sK6
    | ~ spl29_9 ),
    inference(avatar_component_clause,[],[f2475])).

fof(f2475,plain,
    ( spl29_9
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_9])])).

fof(f2511,plain,
    ( spl29_9
    | spl29_11 ),
    inference(avatar_split_clause,[],[f1010,f2509,f2475])).

fof(f1010,plain,
    ( k8_setfam_1(sK4,sK6) = k1_setfam_1(sK6)
    | k1_xboole_0 = sK6 ),
    inference(backward_demodulation,[],[f971,f980])).

fof(f980,plain,(
    k6_setfam_1(sK4,sK6) = k1_setfam_1(sK6) ),
    inference(resolution,[],[f775,f824])).

fof(f824,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f647])).

fof(f647,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f570])).

fof(f570,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f775,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4))) ),
    inference(cnf_transformation,[],[f703])).

fof(f971,plain,
    ( k8_setfam_1(sK4,sK6) = k6_setfam_1(sK4,sK6)
    | k1_xboole_0 = sK6 ),
    inference(resolution,[],[f775,f780])).

fof(f780,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f625])).

fof(f2482,plain,
    ( ~ spl29_2
    | ~ spl29_9 ),
    inference(avatar_contradiction_clause,[],[f2481])).

fof(f2481,plain,
    ( $false
    | ~ spl29_2
    | ~ spl29_9 ),
    inference(subsumption_resolution,[],[f2476,f1705])).

fof(f1705,plain,
    ( k1_xboole_0 != sK6
    | ~ spl29_2 ),
    inference(superposition,[],[f846,f1056])).

fof(f1056,plain,
    ( sK6 = k2_xboole_0(k1_tarski(sK7),sK6)
    | ~ spl29_2 ),
    inference(resolution,[],[f1016,f889])).

fof(f2480,plain,
    ( spl29_9
    | spl29_10 ),
    inference(avatar_split_clause,[],[f1003,f2478,f2475])).

fof(f1003,plain,
    ( r2_hidden(sK20(k1_zfmisc_1(sK4),sK6),sK6)
    | k1_xboole_0 = sK6 ),
    inference(resolution,[],[f775,f844])).

fof(f844,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK20(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f747])).

fof(f747,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(sK20(X0,X1),X1)
        & m1_subset_1(sK20(X0,X1),X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f654,f746])).

fof(f746,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( r2_hidden(sK20(X0,X1),X1)
        & m1_subset_1(sK20(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f654,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f653])).

fof(f653,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f497])).

fof(f497,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

fof(f1040,plain,
    ( spl29_1
    | spl29_4 ),
    inference(avatar_split_clause,[],[f777,f1038,f1012])).

fof(f777,plain,(
    ! [X4] :
      ( r2_hidden(sK5,X4)
      | ~ r2_hidden(X4,sK6)
      | r2_hidden(sK5,k8_setfam_1(sK4,sK6)) ) ),
    inference(cnf_transformation,[],[f703])).

fof(f1034,plain,
    ( ~ spl29_1
    | ~ spl29_3 ),
    inference(avatar_split_clause,[],[f779,f1032,f1012])).

fof(f779,plain,
    ( ~ r2_hidden(sK5,sK7)
    | ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f703])).

fof(f1017,plain,
    ( ~ spl29_1
    | spl29_2 ),
    inference(avatar_split_clause,[],[f778,f1015,f1012])).

fof(f778,plain,
    ( r2_hidden(sK7,sK6)
    | ~ r2_hidden(sK5,k8_setfam_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f703])).
%------------------------------------------------------------------------------
