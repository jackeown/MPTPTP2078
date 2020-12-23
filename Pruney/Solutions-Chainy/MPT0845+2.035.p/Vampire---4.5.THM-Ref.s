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
% DateTime   : Thu Dec  3 12:58:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 190 expanded)
%              Number of leaves         :   21 (  75 expanded)
%              Depth                    :   12
%              Number of atoms          :  299 ( 759 expanded)
%              Number of equality atoms :   62 ( 126 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f529,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f158,f187,f193,f197,f238,f296,f434,f446,f453,f528])).

fof(f528,plain,
    ( spl8_9
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f522,f195,f191,f219])).

fof(f219,plain,
    ( spl8_9
  <=> ! [X9] : ~ r2_hidden(X9,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f191,plain,
    ( spl8_6
  <=> r2_hidden(sK1(sK2(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f195,plain,
    ( spl8_7
  <=> r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f522,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1(sK2(sK0),sK0),sK0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_7 ),
    inference(resolution,[],[f196,f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK2(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f17])).

fof(f17,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(f196,plain,
    ( r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f195])).

fof(f453,plain,
    ( ~ spl8_9
    | ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f447])).

fof(f447,plain,
    ( $false
    | ~ spl8_9
    | ~ spl8_12 ),
    inference(resolution,[],[f237,f220])).

fof(f220,plain,
    ( ! [X9] : ~ r2_hidden(X9,sK0)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f219])).

fof(f237,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl8_12
  <=> r2_hidden(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f446,plain,
    ( spl8_12
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f261,f191,f236])).

fof(f261,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl8_6 ),
    inference(resolution,[],[f192,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK2(X1),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f192,plain,
    ( r2_hidden(sK1(sK2(sK0),sK0),sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f191])).

fof(f434,plain,
    ( spl8_1
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f432,f185,f156,f49])).

fof(f49,plain,
    ( spl8_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f156,plain,
    ( spl8_3
  <=> ! [X1,X0] :
        ( k3_setfam_1(sK0,X0) = X1
        | r2_hidden(sK3(sK0,X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f185,plain,
    ( spl8_5
  <=> ! [X26] : sK0 = k3_setfam_1(sK0,X26) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f432,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(trivial_inequality_removal,[],[f429])).

fof(f429,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(superposition,[],[f348,f27])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f348,plain,
    ( ! [X7] :
        ( k4_xboole_0(X7,k1_tarski(sK2(X7))) != X7
        | sK0 = X7 )
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(resolution,[],[f311,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f311,plain,
    ( ! [X10] :
        ( r2_hidden(sK2(X10),X10)
        | sK0 = X10 )
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f162,f186])).

fof(f186,plain,
    ( ! [X26] : sK0 = k3_setfam_1(sK0,X26)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f185])).

fof(f162,plain,
    ( ! [X10,X9] :
        ( r2_hidden(sK2(X10),X10)
        | k3_setfam_1(sK0,X9) = X10 )
    | ~ spl8_3 ),
    inference(resolution,[],[f157,f33])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK0,X0,X1),X1)
        | k3_setfam_1(sK0,X0) = X1 )
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f156])).

fof(f296,plain,
    ( ~ spl8_4
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f291,f236,f182])).

fof(f182,plain,
    ( spl8_4
  <=> r1_xboole_0(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f291,plain,
    ( ~ r1_xboole_0(sK2(sK0),sK0)
    | ~ spl8_12 ),
    inference(resolution,[],[f237,f26])).

fof(f26,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r1_xboole_0(X1,sK0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK0)
        | ~ r2_hidden(X1,sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).

fof(f12,plain,
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

fof(f9,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f238,plain,
    ( spl8_12
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f226,f153,f236])).

fof(f153,plain,
    ( spl8_2
  <=> r2_hidden(sK1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f226,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f154,f33])).

fof(f154,plain,
    ( r2_hidden(sK1(sK0,sK0),sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f153])).

fof(f197,plain,
    ( spl8_7
    | spl8_4 ),
    inference(avatar_split_clause,[],[f189,f182,f195])).

fof(f189,plain,
    ( r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0))
    | spl8_4 ),
    inference(resolution,[],[f183,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f183,plain,
    ( ~ r1_xboole_0(sK2(sK0),sK0)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f182])).

fof(f193,plain,
    ( spl8_6
    | spl8_4 ),
    inference(avatar_split_clause,[],[f188,f182,f191])).

fof(f188,plain,
    ( r2_hidden(sK1(sK2(sK0),sK0),sK0)
    | spl8_4 ),
    inference(resolution,[],[f183,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f187,plain,
    ( ~ spl8_4
    | spl8_5
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f179,f156,f185,f182])).

fof(f179,plain,
    ( ! [X26] :
        ( sK0 = k3_setfam_1(sK0,X26)
        | ~ r1_xboole_0(sK2(sK0),sK0) )
    | ~ spl8_3 ),
    inference(resolution,[],[f162,f26])).

fof(f158,plain,
    ( spl8_2
    | spl8_3 ),
    inference(avatar_split_clause,[],[f151,f156,f153])).

fof(f151,plain,(
    ! [X0,X1] :
      ( k3_setfam_1(sK0,X0) = X1
      | r2_hidden(sK3(sK0,X0,X1),X1)
      | r2_hidden(sK1(sK0,sK0),sK0) ) ),
    inference(duplicate_literal_removal,[],[f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( k3_setfam_1(sK0,X0) = X1
      | r2_hidden(sK3(sK0,X0,X1),X1)
      | r2_hidden(sK1(sK0,sK0),sK0)
      | k3_setfam_1(sK0,X0) = X1
      | r2_hidden(sK3(sK0,X0,X1),X1) ) ),
    inference(resolution,[],[f120,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(sK4(sK0,X0,X1),sK0),sK0)
      | k3_setfam_1(sK0,X0) = X1
      | r2_hidden(sK3(sK0,X0,X1),X1) ) ),
    inference(resolution,[],[f59,f29])).

fof(f59,plain,(
    ! [X28,X27] :
      ( ~ r1_xboole_0(sK4(sK0,X27,X28),sK0)
      | r2_hidden(sK3(sK0,X27,X28),X28)
      | k3_setfam_1(sK0,X27) = X28 ) ),
    inference(resolution,[],[f39,f26])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | k3_setfam_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_setfam_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k3_xboole_0(X4,X5) != sK3(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( sK3(X0,X1,X2) = k3_xboole_0(sK4(X0,X1,X2),sK5(X0,X1,X2))
              & r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k3_xboole_0(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k3_xboole_0(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
                & r2_hidden(sK7(X0,X1,X8),X1)
                & r2_hidden(sK6(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k3_setfam_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f20,f23,f22,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k3_xboole_0(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k3_xboole_0(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k3_xboole_0(X4,X5) != sK3(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k3_xboole_0(X6,X7) = sK3(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k3_xboole_0(X6,X7) = sK3(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK3(X0,X1,X2) = k3_xboole_0(sK4(X0,X1,X2),sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k3_xboole_0(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k3_xboole_0(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
        & r2_hidden(sK7(X0,X1,X8),X1)
        & r2_hidden(sK6(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k3_setfam_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k3_xboole_0(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k3_xboole_0(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k3_xboole_0(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k3_xboole_0(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k3_setfam_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k3_setfam_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k3_xboole_0(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k3_xboole_0(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k3_xboole_0(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k3_xboole_0(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_setfam_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k3_setfam_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k3_xboole_0(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_setfam_1)).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK1(sK4(sK0,X0,X1),sK0),X2)
      | k3_setfam_1(sK0,X0) = X1
      | r2_hidden(sK3(sK0,X0,X1),X1)
      | r2_hidden(sK1(X2,sK0),sK0) ) ),
    inference(resolution,[],[f66,f29])).

fof(f66,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_xboole_0(X10,sK0)
      | r2_hidden(sK3(sK0,X8,X9),X9)
      | k3_setfam_1(sK0,X8) = X9
      | ~ r2_hidden(sK1(sK4(sK0,X8,X9),sK0),X10) ) ),
    inference(resolution,[],[f61,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f51,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f25,f49])).

fof(f25,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (22368)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.45  % (22368)Refutation not found, incomplete strategy% (22368)------------------------------
% 0.20/0.45  % (22368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (22368)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.45  
% 0.20/0.45  % (22368)Memory used [KB]: 10618
% 0.20/0.45  % (22368)Time elapsed: 0.046 s
% 0.20/0.45  % (22368)------------------------------
% 0.20/0.45  % (22368)------------------------------
% 0.20/0.47  % (22348)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (22355)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (22363)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (22363)Refutation not found, incomplete strategy% (22363)------------------------------
% 0.20/0.48  % (22363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (22363)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (22363)Memory used [KB]: 6140
% 0.20/0.48  % (22363)Time elapsed: 0.065 s
% 0.20/0.48  % (22363)------------------------------
% 0.20/0.48  % (22363)------------------------------
% 0.20/0.48  % (22360)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (22362)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (22356)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (22348)Refutation not found, incomplete strategy% (22348)------------------------------
% 0.20/0.49  % (22348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (22348)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (22348)Memory used [KB]: 6140
% 0.20/0.49  % (22348)Time elapsed: 0.050 s
% 0.20/0.49  % (22348)------------------------------
% 0.20/0.49  % (22348)------------------------------
% 0.20/0.49  % (22350)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (22353)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (22354)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (22365)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.49  % (22367)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.49  % (22364)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.50  % (22357)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.50  % (22351)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (22349)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (22351)Refutation not found, incomplete strategy% (22351)------------------------------
% 0.20/0.50  % (22351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (22351)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (22351)Memory used [KB]: 10618
% 0.20/0.50  % (22351)Time elapsed: 0.093 s
% 0.20/0.50  % (22351)------------------------------
% 0.20/0.50  % (22351)------------------------------
% 0.20/0.50  % (22358)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  % (22349)Refutation not found, incomplete strategy% (22349)------------------------------
% 0.20/0.50  % (22349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (22349)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (22349)Memory used [KB]: 10618
% 0.20/0.50  % (22349)Time elapsed: 0.073 s
% 0.20/0.50  % (22349)------------------------------
% 0.20/0.50  % (22349)------------------------------
% 0.20/0.50  % (22358)Refutation not found, incomplete strategy% (22358)------------------------------
% 0.20/0.50  % (22358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (22361)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.51  % (22359)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.51  % (22352)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.51  % (22359)Refutation not found, incomplete strategy% (22359)------------------------------
% 0.20/0.51  % (22359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (22359)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (22359)Memory used [KB]: 10618
% 0.20/0.51  % (22359)Time elapsed: 0.109 s
% 0.20/0.51  % (22359)------------------------------
% 0.20/0.51  % (22359)------------------------------
% 0.20/0.51  % (22354)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f529,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f51,f158,f187,f193,f197,f238,f296,f434,f446,f453,f528])).
% 0.20/0.51  fof(f528,plain,(
% 0.20/0.51    spl8_9 | ~spl8_6 | ~spl8_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f522,f195,f191,f219])).
% 0.20/0.51  fof(f219,plain,(
% 0.20/0.51    spl8_9 <=> ! [X9] : ~r2_hidden(X9,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.20/0.51  fof(f191,plain,(
% 0.20/0.51    spl8_6 <=> r2_hidden(sK1(sK2(sK0),sK0),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.51  fof(f195,plain,(
% 0.20/0.51    spl8_7 <=> r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.51  fof(f522,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(sK1(sK2(sK0),sK0),sK0) | ~r2_hidden(X0,sK0)) ) | ~spl8_7),
% 0.20/0.51    inference(resolution,[],[f196,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).
% 0.20/0.51  fof(f196,plain,(
% 0.20/0.51    r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0)) | ~spl8_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f195])).
% 0.20/0.51  fof(f453,plain,(
% 0.20/0.51    ~spl8_9 | ~spl8_12),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f447])).
% 0.20/0.51  fof(f447,plain,(
% 0.20/0.51    $false | (~spl8_9 | ~spl8_12)),
% 0.20/0.51    inference(resolution,[],[f237,f220])).
% 0.20/0.51  fof(f220,plain,(
% 0.20/0.51    ( ! [X9] : (~r2_hidden(X9,sK0)) ) | ~spl8_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f219])).
% 0.20/0.51  fof(f237,plain,(
% 0.20/0.51    r2_hidden(sK2(sK0),sK0) | ~spl8_12),
% 0.20/0.51    inference(avatar_component_clause,[],[f236])).
% 0.20/0.51  fof(f236,plain,(
% 0.20/0.51    spl8_12 <=> r2_hidden(sK2(sK0),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.20/0.51  fof(f446,plain,(
% 0.20/0.51    spl8_12 | ~spl8_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f261,f191,f236])).
% 0.20/0.51  fof(f261,plain,(
% 0.20/0.51    r2_hidden(sK2(sK0),sK0) | ~spl8_6),
% 0.20/0.51    inference(resolution,[],[f192,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK2(X1),X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f192,plain,(
% 0.20/0.51    r2_hidden(sK1(sK2(sK0),sK0),sK0) | ~spl8_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f191])).
% 0.20/0.51  fof(f434,plain,(
% 0.20/0.51    spl8_1 | ~spl8_3 | ~spl8_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f432,f185,f156,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    spl8_1 <=> k1_xboole_0 = sK0),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.51  fof(f156,plain,(
% 0.20/0.51    spl8_3 <=> ! [X1,X0] : (k3_setfam_1(sK0,X0) = X1 | r2_hidden(sK3(sK0,X0,X1),X1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.51  fof(f185,plain,(
% 0.20/0.51    spl8_5 <=> ! [X26] : sK0 = k3_setfam_1(sK0,X26)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.51  fof(f432,plain,(
% 0.20/0.51    k1_xboole_0 = sK0 | (~spl8_3 | ~spl8_5)),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f429])).
% 0.20/0.51  fof(f429,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | (~spl8_3 | ~spl8_5)),
% 0.20/0.51    inference(superposition,[],[f348,f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.20/0.51  fof(f348,plain,(
% 0.20/0.51    ( ! [X7] : (k4_xboole_0(X7,k1_tarski(sK2(X7))) != X7 | sK0 = X7) ) | (~spl8_3 | ~spl8_5)),
% 0.20/0.51    inference(resolution,[],[f311,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.20/0.51  fof(f311,plain,(
% 0.20/0.51    ( ! [X10] : (r2_hidden(sK2(X10),X10) | sK0 = X10) ) | (~spl8_3 | ~spl8_5)),
% 0.20/0.51    inference(forward_demodulation,[],[f162,f186])).
% 0.20/0.51  fof(f186,plain,(
% 0.20/0.51    ( ! [X26] : (sK0 = k3_setfam_1(sK0,X26)) ) | ~spl8_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f185])).
% 0.20/0.51  fof(f162,plain,(
% 0.20/0.51    ( ! [X10,X9] : (r2_hidden(sK2(X10),X10) | k3_setfam_1(sK0,X9) = X10) ) | ~spl8_3),
% 0.20/0.51    inference(resolution,[],[f157,f33])).
% 0.20/0.51  fof(f157,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK3(sK0,X0,X1),X1) | k3_setfam_1(sK0,X0) = X1) ) | ~spl8_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f156])).
% 0.20/0.51  fof(f296,plain,(
% 0.20/0.51    ~spl8_4 | ~spl8_12),
% 0.20/0.51    inference(avatar_split_clause,[],[f291,f236,f182])).
% 0.20/0.51  fof(f182,plain,(
% 0.20/0.51    spl8_4 <=> r1_xboole_0(sK2(sK0),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.51  fof(f291,plain,(
% 0.20/0.51    ~r1_xboole_0(sK2(sK0),sK0) | ~spl8_12),
% 0.20/0.51    inference(resolution,[],[f237,f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X1] : (~r2_hidden(X1,sK0) | ~r1_xboole_0(X1,sK0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0) => (! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0)),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.51    inference(negated_conjecture,[],[f6])).
% 0.20/0.51  fof(f6,conjecture,(
% 0.20/0.51    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).
% 0.20/0.51  fof(f238,plain,(
% 0.20/0.51    spl8_12 | ~spl8_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f226,f153,f236])).
% 0.20/0.51  fof(f153,plain,(
% 0.20/0.51    spl8_2 <=> r2_hidden(sK1(sK0,sK0),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.51  fof(f226,plain,(
% 0.20/0.51    r2_hidden(sK2(sK0),sK0) | ~spl8_2),
% 0.20/0.51    inference(resolution,[],[f154,f33])).
% 0.20/0.51  fof(f154,plain,(
% 0.20/0.51    r2_hidden(sK1(sK0,sK0),sK0) | ~spl8_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f153])).
% 0.20/0.51  fof(f197,plain,(
% 0.20/0.51    spl8_7 | spl8_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f189,f182,f195])).
% 0.20/0.52  fof(f189,plain,(
% 0.20/0.52    r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0)) | spl8_4),
% 0.20/0.52    inference(resolution,[],[f183,f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,plain,(
% 0.20/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.52    inference(rectify,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.52  fof(f183,plain,(
% 0.20/0.52    ~r1_xboole_0(sK2(sK0),sK0) | spl8_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f182])).
% 0.20/0.52  fof(f193,plain,(
% 0.20/0.52    spl8_6 | spl8_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f188,f182,f191])).
% 0.20/0.52  fof(f188,plain,(
% 0.20/0.52    r2_hidden(sK1(sK2(sK0),sK0),sK0) | spl8_4),
% 0.20/0.52    inference(resolution,[],[f183,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f187,plain,(
% 0.20/0.52    ~spl8_4 | spl8_5 | ~spl8_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f179,f156,f185,f182])).
% 0.20/0.52  fof(f179,plain,(
% 0.20/0.52    ( ! [X26] : (sK0 = k3_setfam_1(sK0,X26) | ~r1_xboole_0(sK2(sK0),sK0)) ) | ~spl8_3),
% 0.20/0.52    inference(resolution,[],[f162,f26])).
% 0.20/0.52  fof(f158,plain,(
% 0.20/0.52    spl8_2 | spl8_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f151,f156,f153])).
% 0.20/0.52  fof(f151,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k3_setfam_1(sK0,X0) = X1 | r2_hidden(sK3(sK0,X0,X1),X1) | r2_hidden(sK1(sK0,sK0),sK0)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f148])).
% 0.20/0.52  fof(f148,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k3_setfam_1(sK0,X0) = X1 | r2_hidden(sK3(sK0,X0,X1),X1) | r2_hidden(sK1(sK0,sK0),sK0) | k3_setfam_1(sK0,X0) = X1 | r2_hidden(sK3(sK0,X0,X1),X1)) )),
% 0.20/0.52    inference(resolution,[],[f120,f61])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(sK1(sK4(sK0,X0,X1),sK0),sK0) | k3_setfam_1(sK0,X0) = X1 | r2_hidden(sK3(sK0,X0,X1),X1)) )),
% 0.20/0.52    inference(resolution,[],[f59,f29])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X28,X27] : (~r1_xboole_0(sK4(sK0,X27,X28),sK0) | r2_hidden(sK3(sK0,X27,X28),X28) | k3_setfam_1(sK0,X27) = X28) )),
% 0.20/0.52    inference(resolution,[],[f39,f26])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | k3_setfam_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((k3_setfam_1(X0,X1) = X2 | ((! [X4,X5] : (k3_xboole_0(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((sK3(X0,X1,X2) = k3_xboole_0(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k3_xboole_0(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k3_xboole_0(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k3_setfam_1(X0,X1) != X2))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f20,f23,f22,f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k3_xboole_0(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k3_xboole_0(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k3_xboole_0(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X7,X6] : (k3_xboole_0(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X2,X1,X0] : (? [X7,X6] : (k3_xboole_0(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK3(X0,X1,X2) = k3_xboole_0(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X8,X1,X0] : (? [X11,X12] : (k3_xboole_0(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k3_xboole_0(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((k3_setfam_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k3_xboole_0(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k3_xboole_0(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k3_xboole_0(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k3_xboole_0(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k3_setfam_1(X0,X1) != X2))),
% 0.20/0.52    inference(rectify,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((k3_setfam_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k3_xboole_0(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k3_xboole_0(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k3_xboole_0(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k3_xboole_0(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k3_setfam_1(X0,X1) != X2))),
% 0.20/0.52    inference(nnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (k3_setfam_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k3_xboole_0(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_setfam_1)).
% 0.20/0.52  fof(f120,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(sK1(sK4(sK0,X0,X1),sK0),X2) | k3_setfam_1(sK0,X0) = X1 | r2_hidden(sK3(sK0,X0,X1),X1) | r2_hidden(sK1(X2,sK0),sK0)) )),
% 0.20/0.52    inference(resolution,[],[f66,f29])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    ( ! [X10,X8,X9] : (~r1_xboole_0(X10,sK0) | r2_hidden(sK3(sK0,X8,X9),X9) | k3_setfam_1(sK0,X8) = X9 | ~r2_hidden(sK1(sK4(sK0,X8,X9),sK0),X10)) )),
% 0.20/0.52    inference(resolution,[],[f61,f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ~spl8_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f25,f49])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    k1_xboole_0 != sK0),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (22354)------------------------------
% 0.20/0.52  % (22354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (22354)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (22354)Memory used [KB]: 11001
% 0.20/0.52  % (22354)Time elapsed: 0.072 s
% 0.20/0.52  % (22354)------------------------------
% 0.20/0.52  % (22354)------------------------------
% 0.20/0.52  % (22366)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.52  % (22347)Success in time 0.163 s
%------------------------------------------------------------------------------
