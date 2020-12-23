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
% DateTime   : Thu Dec  3 12:58:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 184 expanded)
%              Number of leaves         :   23 (  72 expanded)
%              Depth                    :   15
%              Number of atoms          :  288 ( 697 expanded)
%              Number of equality atoms :   36 (  80 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f338,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f58,f63,f132,f177,f183,f187,f199,f311,f335,f337])).

fof(f337,plain,
    ( ~ spl6_12
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f230,f197,f175])).

fof(f175,plain,
    ( spl6_12
  <=> r1_xboole_0(sK5(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f197,plain,
    ( spl6_16
  <=> r2_hidden(sK5(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f230,plain,
    ( ~ r1_xboole_0(sK5(sK0),sK0)
    | ~ spl6_16 ),
    inference(resolution,[],[f198,f31])).

fof(f31,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r1_xboole_0(X1,sK0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK0)
        | ~ r2_hidden(X1,sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ r1_xboole_0(X1,X0)
            | ~ r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 )
   => ( ! [X1] :
          ( ~ r1_xboole_0(X1,sK0)
          | ~ r2_hidden(X1,sK0) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f198,plain,
    ( r2_hidden(sK5(sK0),sK0)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f197])).

fof(f335,plain,
    ( ~ spl6_13
    | ~ spl6_28 ),
    inference(avatar_contradiction_clause,[],[f329])).

fof(f329,plain,
    ( $false
    | ~ spl6_13
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f182,f309])).

fof(f309,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl6_28
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f182,plain,
    ( r2_hidden(sK4(sK5(sK0),sK0),sK0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl6_13
  <=> r2_hidden(sK4(sK5(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f311,plain,
    ( spl6_28
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f303,f185,f181,f308])).

fof(f185,plain,
    ( spl6_14
  <=> r2_hidden(sK4(sK5(sK0),sK0),sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f303,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK5(sK0),sK0),sK0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_14 ),
    inference(resolution,[],[f186,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK5(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK5(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK5(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f28])).

fof(f28,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK5(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK5(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f186,plain,
    ( r2_hidden(sK4(sK5(sK0),sK0),sK5(sK0))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f185])).

fof(f199,plain,
    ( spl6_16
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f190,f127,f197])).

fof(f127,plain,
    ( spl6_6
  <=> r2_hidden(sK4(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f190,plain,
    ( r2_hidden(sK5(sK0),sK0)
    | ~ spl6_6 ),
    inference(resolution,[],[f128,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK5(X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f128,plain,
    ( r2_hidden(sK4(sK0,sK0),sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f187,plain,
    ( spl6_14
    | spl6_12 ),
    inference(avatar_split_clause,[],[f179,f175,f185])).

fof(f179,plain,
    ( r2_hidden(sK4(sK5(sK0),sK0),sK5(sK0))
    | spl6_12 ),
    inference(resolution,[],[f176,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f176,plain,
    ( ~ r1_xboole_0(sK5(sK0),sK0)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f175])).

fof(f183,plain,
    ( spl6_13
    | spl6_12 ),
    inference(avatar_split_clause,[],[f178,f175,f181])).

fof(f178,plain,
    ( r2_hidden(sK4(sK5(sK0),sK0),sK0)
    | spl6_12 ),
    inference(resolution,[],[f176,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f177,plain,
    ( ~ spl6_12
    | spl6_1
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f172,f130,f52,f175])).

fof(f52,plain,
    ( spl6_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f130,plain,
    ( spl6_7
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK1(k1_xboole_0,sK0,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f172,plain,
    ( k1_xboole_0 = sK0
    | ~ r1_xboole_0(sK5(sK0),sK0)
    | ~ spl6_7 ),
    inference(resolution,[],[f135,f31])).

fof(f135,plain,
    ( ! [X4] :
        ( r2_hidden(sK5(X4),X4)
        | k1_xboole_0 = X4 )
    | ~ spl6_7 ),
    inference(resolution,[],[f131,f46])).

fof(f131,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(k1_xboole_0,sK0,X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f130])).

fof(f132,plain,
    ( spl6_6
    | spl6_7
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f125,f61,f130,f127])).

fof(f61,plain,
    ( spl6_3
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f125,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK1(k1_xboole_0,sK0,X0),X0)
        | r2_hidden(sK4(sK0,sK0),sK0) )
    | ~ spl6_3 ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK1(k1_xboole_0,sK0,X0),X0)
        | r2_hidden(sK4(sK0,sK0),sK0)
        | k1_xboole_0 = X0
        | r2_hidden(sK1(k1_xboole_0,sK0,X0),X0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f110,f87])).

fof(f87,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2(k1_xboole_0,sK0,X0),sK0),sK0)
        | k1_xboole_0 = X0
        | r2_hidden(sK1(k1_xboole_0,sK0,X0),X0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f85,f43])).

fof(f85,plain,
    ( ! [X17] :
        ( ~ r1_xboole_0(sK2(k1_xboole_0,sK0,X17),sK0)
        | r2_hidden(sK1(k1_xboole_0,sK0,X17),X17)
        | k1_xboole_0 = X17 )
    | ~ spl6_3 ),
    inference(resolution,[],[f77,f31])).

fof(f77,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK2(k1_xboole_0,X3,X4),X3)
        | k1_xboole_0 = X4
        | r2_hidden(sK1(k1_xboole_0,X3,X4),X4) )
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f76,f34])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

fof(f76,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK2(k1_xboole_0,X3,X4),X3)
        | r2_hidden(sK1(k1_xboole_0,X3,X4),X4)
        | k10_relat_1(k1_xboole_0,X3) = X4 )
    | ~ spl6_3 ),
    inference(resolution,[],[f40,f62])).

fof(f62,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | k10_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK1(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK2(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) )
                | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK3(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f24,f23,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(f110,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK4(sK2(k1_xboole_0,sK0,X0),sK0),X1)
        | k1_xboole_0 = X0
        | r2_hidden(sK1(k1_xboole_0,sK0,X0),X0)
        | r2_hidden(sK4(X1,sK0),sK0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f90,f43])).

fof(f90,plain,
    ( ! [X2,X1] :
        ( ~ r1_xboole_0(X2,sK0)
        | r2_hidden(sK1(k1_xboole_0,sK0,X1),X1)
        | k1_xboole_0 = X1
        | ~ r2_hidden(sK4(sK2(k1_xboole_0,sK0,X1),sK0),X2) )
    | ~ spl6_3 ),
    inference(resolution,[],[f87,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,
    ( spl6_3
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f59,f56,f61])).

fof(f56,plain,
    ( spl6_2
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f59,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_2 ),
    inference(superposition,[],[f35,f57])).

fof(f57,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f35,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f58,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f32,f56])).

fof(f32,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f54,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f30,f52])).

fof(f30,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (18186)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.45  % (18177)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.46  % (18177)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f338,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f54,f58,f63,f132,f177,f183,f187,f199,f311,f335,f337])).
% 0.21/0.46  fof(f337,plain,(
% 0.21/0.46    ~spl6_12 | ~spl6_16),
% 0.21/0.46    inference(avatar_split_clause,[],[f230,f197,f175])).
% 0.21/0.46  fof(f175,plain,(
% 0.21/0.46    spl6_12 <=> r1_xboole_0(sK5(sK0),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.46  fof(f197,plain,(
% 0.21/0.46    spl6_16 <=> r2_hidden(sK5(sK0),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.46  fof(f230,plain,(
% 0.21/0.46    ~r1_xboole_0(sK5(sK0),sK0) | ~spl6_16),
% 0.21/0.46    inference(resolution,[],[f198,f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X1] : (~r2_hidden(X1,sK0) | ~r1_xboole_0(X1,sK0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0) => (! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0)),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.46    inference(ennf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,negated_conjecture,(
% 0.21/0.46    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.46    inference(negated_conjecture,[],[f9])).
% 0.21/0.46  fof(f9,conjecture,(
% 0.21/0.46    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).
% 0.21/0.46  fof(f198,plain,(
% 0.21/0.46    r2_hidden(sK5(sK0),sK0) | ~spl6_16),
% 0.21/0.46    inference(avatar_component_clause,[],[f197])).
% 0.21/0.46  fof(f335,plain,(
% 0.21/0.46    ~spl6_13 | ~spl6_28),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f329])).
% 0.21/0.46  fof(f329,plain,(
% 0.21/0.46    $false | (~spl6_13 | ~spl6_28)),
% 0.21/0.46    inference(subsumption_resolution,[],[f182,f309])).
% 0.21/0.46  fof(f309,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl6_28),
% 0.21/0.46    inference(avatar_component_clause,[],[f308])).
% 0.21/0.46  fof(f308,plain,(
% 0.21/0.46    spl6_28 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.21/0.46  fof(f182,plain,(
% 0.21/0.46    r2_hidden(sK4(sK5(sK0),sK0),sK0) | ~spl6_13),
% 0.21/0.46    inference(avatar_component_clause,[],[f181])).
% 0.21/0.46  fof(f181,plain,(
% 0.21/0.46    spl6_13 <=> r2_hidden(sK4(sK5(sK0),sK0),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.46  fof(f311,plain,(
% 0.21/0.46    spl6_28 | ~spl6_13 | ~spl6_14),
% 0.21/0.46    inference(avatar_split_clause,[],[f303,f185,f181,f308])).
% 0.21/0.46  fof(f185,plain,(
% 0.21/0.46    spl6_14 <=> r2_hidden(sK4(sK5(sK0),sK0),sK5(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.46  fof(f303,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(sK4(sK5(sK0),sK0),sK0) | ~r2_hidden(X0,sK0)) ) | ~spl6_14),
% 0.21/0.46    inference(resolution,[],[f186,f47])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK5(X1),X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK5(X1),X1)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).
% 0.21/0.47  fof(f186,plain,(
% 0.21/0.47    r2_hidden(sK4(sK5(sK0),sK0),sK5(sK0)) | ~spl6_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f185])).
% 0.21/0.47  fof(f199,plain,(
% 0.21/0.47    spl6_16 | ~spl6_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f190,f127,f197])).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    spl6_6 <=> r2_hidden(sK4(sK0,sK0),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.47  fof(f190,plain,(
% 0.21/0.47    r2_hidden(sK5(sK0),sK0) | ~spl6_6),
% 0.21/0.47    inference(resolution,[],[f128,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK5(X1),X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f29])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    r2_hidden(sK4(sK0,sK0),sK0) | ~spl6_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f127])).
% 0.21/0.47  fof(f187,plain,(
% 0.21/0.47    spl6_14 | spl6_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f179,f175,f185])).
% 0.21/0.47  fof(f179,plain,(
% 0.21/0.47    r2_hidden(sK4(sK5(sK0),sK0),sK5(sK0)) | spl6_12),
% 0.21/0.47    inference(resolution,[],[f176,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(rectify,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.47  fof(f176,plain,(
% 0.21/0.47    ~r1_xboole_0(sK5(sK0),sK0) | spl6_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f175])).
% 0.21/0.47  fof(f183,plain,(
% 0.21/0.47    spl6_13 | spl6_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f178,f175,f181])).
% 0.21/0.47  fof(f178,plain,(
% 0.21/0.47    r2_hidden(sK4(sK5(sK0),sK0),sK0) | spl6_12),
% 0.21/0.47    inference(resolution,[],[f176,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f177,plain,(
% 0.21/0.47    ~spl6_12 | spl6_1 | ~spl6_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f172,f130,f52,f175])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    spl6_1 <=> k1_xboole_0 = sK0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    spl6_7 <=> ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK1(k1_xboole_0,sK0,X0),X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.47  fof(f172,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | ~r1_xboole_0(sK5(sK0),sK0) | ~spl6_7),
% 0.21/0.47    inference(resolution,[],[f135,f31])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    ( ! [X4] : (r2_hidden(sK5(X4),X4) | k1_xboole_0 = X4) ) | ~spl6_7),
% 0.21/0.47    inference(resolution,[],[f131,f46])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(sK1(k1_xboole_0,sK0,X0),X0) | k1_xboole_0 = X0) ) | ~spl6_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f130])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    spl6_6 | spl6_7 | ~spl6_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f125,f61,f130,f127])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    spl6_3 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK1(k1_xboole_0,sK0,X0),X0) | r2_hidden(sK4(sK0,sK0),sK0)) ) | ~spl6_3),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f122])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK1(k1_xboole_0,sK0,X0),X0) | r2_hidden(sK4(sK0,sK0),sK0) | k1_xboole_0 = X0 | r2_hidden(sK1(k1_xboole_0,sK0,X0),X0)) ) | ~spl6_3),
% 0.21/0.47    inference(resolution,[],[f110,f87])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(sK4(sK2(k1_xboole_0,sK0,X0),sK0),sK0) | k1_xboole_0 = X0 | r2_hidden(sK1(k1_xboole_0,sK0,X0),X0)) ) | ~spl6_3),
% 0.21/0.47    inference(resolution,[],[f85,f43])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    ( ! [X17] : (~r1_xboole_0(sK2(k1_xboole_0,sK0,X17),sK0) | r2_hidden(sK1(k1_xboole_0,sK0,X17),X17) | k1_xboole_0 = X17) ) | ~spl6_3),
% 0.21/0.47    inference(resolution,[],[f77,f31])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    ( ! [X4,X3] : (r2_hidden(sK2(k1_xboole_0,X3,X4),X3) | k1_xboole_0 = X4 | r2_hidden(sK1(k1_xboole_0,X3,X4),X4)) ) | ~spl6_3),
% 0.21/0.47    inference(forward_demodulation,[],[f76,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ( ! [X4,X3] : (r2_hidden(sK2(k1_xboole_0,X3,X4),X3) | r2_hidden(sK1(k1_xboole_0,X3,X4),X4) | k10_relat_1(k1_xboole_0,X3) = X4) ) | ~spl6_3),
% 0.21/0.47    inference(resolution,[],[f40,f62])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    v1_relat_1(k1_xboole_0) | ~spl6_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f61])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2) | k10_relat_1(X0,X1) = X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f24,f23,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0)) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(rectify,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(sK4(sK2(k1_xboole_0,sK0,X0),sK0),X1) | k1_xboole_0 = X0 | r2_hidden(sK1(k1_xboole_0,sK0,X0),X0) | r2_hidden(sK4(X1,sK0),sK0)) ) | ~spl6_3),
% 0.21/0.47    inference(resolution,[],[f90,f43])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    ( ! [X2,X1] : (~r1_xboole_0(X2,sK0) | r2_hidden(sK1(k1_xboole_0,sK0,X1),X1) | k1_xboole_0 = X1 | ~r2_hidden(sK4(sK2(k1_xboole_0,sK0,X1),sK0),X2)) ) | ~spl6_3),
% 0.21/0.47    inference(resolution,[],[f87,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl6_3 | ~spl6_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f59,f56,f61])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    spl6_2 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    v1_relat_1(k1_xboole_0) | ~spl6_2),
% 0.21/0.47    inference(superposition,[],[f35,f57])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl6_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f56])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.47    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl6_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f32,f56])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ~spl6_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f30,f52])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    k1_xboole_0 != sK0),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (18177)------------------------------
% 0.21/0.47  % (18177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (18177)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (18177)Memory used [KB]: 10874
% 0.21/0.47  % (18177)Time elapsed: 0.018 s
% 0.21/0.47  % (18177)------------------------------
% 0.21/0.47  % (18177)------------------------------
% 0.21/0.47  % (18182)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.47  % (18167)Success in time 0.116 s
%------------------------------------------------------------------------------
