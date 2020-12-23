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
% DateTime   : Thu Dec  3 12:42:44 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 188 expanded)
%              Number of leaves         :   21 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  279 ( 662 expanded)
%              Number of equality atoms :   43 (  93 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f426,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f86,f88,f271,f321,f341,f403,f420,f425])).

fof(f425,plain,
    ( spl7_1
    | ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f424])).

fof(f424,plain,
    ( $false
    | spl7_1
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f423,f60])).

fof(f60,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl7_1
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f423,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl7_8 ),
    inference(duplicate_literal_removal,[],[f421])).

fof(f421,plain,
    ( r1_tarski(sK0,sK2)
    | r1_tarski(sK0,sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f363,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f363,plain,
    ( ! [X9] :
        ( r2_hidden(sK6(sK0,X9),sK2)
        | r1_tarski(sK0,X9) )
    | ~ spl7_8 ),
    inference(resolution,[],[f251,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f251,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK0)
        | r2_hidden(X2,sK2) )
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl7_8
  <=> ! [X2] :
        ( ~ r2_hidden(X2,sK0)
        | r2_hidden(X2,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f420,plain,
    ( spl7_2
    | ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f419])).

fof(f419,plain,
    ( $false
    | spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f418,f64])).

fof(f64,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl7_2
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f418,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl7_5 ),
    inference(duplicate_literal_removal,[],[f416])).

fof(f416,plain,
    ( r1_tarski(sK1,sK3)
    | r1_tarski(sK1,sK3)
    | ~ spl7_5 ),
    inference(resolution,[],[f352,f46])).

fof(f352,plain,
    ( ! [X9] :
        ( r2_hidden(sK6(sK1,X9),sK3)
        | r1_tarski(sK1,X9) )
    | ~ spl7_5 ),
    inference(resolution,[],[f241,f45])).

fof(f241,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | r2_hidden(X1,sK3) )
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl7_5
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | r2_hidden(X1,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f403,plain,
    ( spl7_7
    | spl7_8 ),
    inference(avatar_split_clause,[],[f401,f250,f247])).

fof(f247,plain,
    ( spl7_7
  <=> ! [X3] : ~ r2_hidden(X3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f401,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(X2,sK2) ) ),
    inference(resolution,[],[f182,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f182,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3))
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f114,f33])).

fof(f33,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ~ r1_tarski(sK1,sK3)
      | ~ r1_tarski(sK0,sK2) )
    & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f18])).

fof(f18,plain,
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

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f114,plain,(
    ! [X12,X10,X8,X11,X9] :
      ( ~ r1_tarski(k2_zfmisc_1(X11,X9),X12)
      | ~ r2_hidden(X10,X11)
      | r2_hidden(k4_tarski(X10,X8),X12)
      | ~ r2_hidden(X8,X9) ) ),
    inference(resolution,[],[f52,f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f341,plain,
    ( spl7_5
    | spl7_6 ),
    inference(avatar_split_clause,[],[f338,f243,f240])).

fof(f243,plain,
    ( spl7_6
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f338,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,sK1)
      | r2_hidden(X1,sK3) ) ),
    inference(resolution,[],[f182,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f321,plain,
    ( ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f320])).

fof(f320,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f317,f56])).

fof(f56,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f317,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f34,f308])).

fof(f308,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(resolution,[],[f244,f101])).

fof(f101,plain,
    ( ! [X3] :
        ( r2_hidden(sK5(X3,k1_xboole_0),X3)
        | k1_xboole_0 = X3 )
    | ~ spl7_4 ),
    inference(resolution,[],[f42,f83])).

fof(f83,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl7_4
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK5(X0,X1),X1)
          | ~ r2_hidden(sK5(X0,X1),X0) )
        & ( r2_hidden(sK5(X0,X1),X1)
          | r2_hidden(sK5(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1),X1)
          | ~ r2_hidden(sK5(X0,X1),X0) )
        & ( r2_hidden(sK5(X0,X1),X1)
          | r2_hidden(sK5(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f244,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f243])).

fof(f34,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f271,plain,
    ( ~ spl7_4
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f270])).

fof(f270,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f267,f55])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f267,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f34,f257])).

fof(f257,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_4
    | ~ spl7_7 ),
    inference(resolution,[],[f248,f101])).

fof(f248,plain,
    ( ! [X3] : ~ r2_hidden(X3,sK1)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f247])).

fof(f88,plain,(
    ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f87])).

fof(f87,plain,
    ( $false
    | ~ spl7_3 ),
    inference(resolution,[],[f80,f36])).

fof(f36,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f80,plain,
    ( ! [X0] : ~ r1_xboole_0(k1_xboole_0,X0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl7_3
  <=> ! [X0] : ~ r1_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f86,plain,
    ( spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f76,f82,f79])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f53,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f65,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f35,f62,f58])).

fof(f35,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:10:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (29672)dis+1002_5_av=off:cond=on:gs=on:lma=on:nm=2:nwc=1:sd=3:ss=axioms:st=1.5:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (29663)lrs+11_4_av=off:gsp=input_only:irw=on:lma=on:nm=0:nwc=1.2:stl=30:sd=2:ss=axioms:sp=reverse_arity:urr=on:updr=off_8 on theBenchmark
% 0.22/0.52  % (29681)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (29672)Refutation not found, incomplete strategy% (29672)------------------------------
% 0.22/0.52  % (29672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (29672)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (29672)Memory used [KB]: 6140
% 0.22/0.52  % (29672)Time elapsed: 0.106 s
% 0.22/0.52  % (29672)------------------------------
% 0.22/0.52  % (29672)------------------------------
% 0.22/0.52  % (29673)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (29665)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_6 on theBenchmark
% 0.22/0.53  % (29685)ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=input_only:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_49 on theBenchmark
% 0.22/0.53  % (29664)dis+1004_1_aac=none:acc=on:afp=40000:afq=1.2:anc=none:cond=on:fde=unused:gs=on:gsem=off:irw=on:nm=32:nwc=2:sd=1:ss=axioms:sos=theory:sp=reverse_arity:urr=ec_only_17 on theBenchmark
% 0.22/0.54  % (29658)lrs-11_3_av=off:bs=unit_only:bsr=on:cond=on:gsp=input_only:gs=on:gsem=on:lma=on:nm=2:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_11 on theBenchmark
% 0.22/0.54  % (29662)dis+4_8:1_add=large:afp=100000:afq=1.4:ep=RST:fde=unused:gsp=input_only:lcm=predicate:nwc=1:sos=all:sp=occurrence:updr=off:uhcvi=on_33 on theBenchmark
% 0.22/0.54  % (29675)lrs-2_3:2_av=off:bce=on:cond=on:gsp=input_only:gs=on:gsem=on:lcm=predicate:lma=on:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off:uhcvi=on_62 on theBenchmark
% 0.22/0.54  % (29671)dis+4_2_av=off:bs=on:fsr=off:gsp=input_only:newcnf=on:nwc=1:sd=3:ss=axioms:st=3.0:sos=all:sp=reverse_arity:urr=ec_only:updr=off_127 on theBenchmark
% 0.22/0.54  % (29661)lrs+2_5:4_av=off:bce=on:cond=fast:ep=R:fde=none:gs=on:lcm=reverse:lwlo=on:nwc=1:stl=30:sd=1:ss=axioms:sos=all:sp=occurrence_8 on theBenchmark
% 0.22/0.54  % (29676)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (29659)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.55  % (29670)dis+10_5:4_add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence:urr=on:updr=off_15 on theBenchmark
% 1.44/0.55  % (29678)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=2.0:amm=sco:anc=none:gs=on:gsem=off:lma=on:lwlo=on:nm=4:nwc=10:stl=30:sd=3:ss=axioms:sos=all:sac=on_49 on theBenchmark
% 1.44/0.55  % (29687)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_48 on theBenchmark
% 1.44/0.55  % (29675)Refutation not found, incomplete strategy% (29675)------------------------------
% 1.44/0.55  % (29675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (29675)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (29675)Memory used [KB]: 6140
% 1.44/0.55  % (29675)Time elapsed: 0.122 s
% 1.44/0.55  % (29675)------------------------------
% 1.44/0.55  % (29675)------------------------------
% 1.44/0.55  % (29676)Refutation not found, incomplete strategy% (29676)------------------------------
% 1.44/0.55  % (29676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (29676)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (29676)Memory used [KB]: 10618
% 1.44/0.55  % (29676)Time elapsed: 0.140 s
% 1.44/0.55  % (29676)------------------------------
% 1.44/0.55  % (29676)------------------------------
% 1.44/0.55  % (29683)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_88 on theBenchmark
% 1.44/0.55  % (29669)dis+1010_2:3_afr=on:afp=40000:afq=1.4:amm=off:anc=none:lma=on:nm=16:nwc=1:sp=occurrence:updr=off:uhcvi=on_34 on theBenchmark
% 1.44/0.56  % (29679)ott+11_4:1_awrs=converge:awrsf=16:acc=model:add=large:afr=on:afp=4000:afq=1.4:amm=off:br=off:cond=fast:fde=none:gsp=input_only:nm=64:nwc=2:nicw=on:sd=3:ss=axioms:s2a=on:sac=on:sp=frequency:urr=on:updr=off_70 on theBenchmark
% 1.44/0.56  % (29677)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_6 on theBenchmark
% 1.44/0.56  % (29684)dis+11_2_add=large:afr=on:anc=none:gs=on:gsem=on:lwlo=on:nm=16:nwc=1:sd=1:ss=axioms:st=3.0:sos=on_4 on theBenchmark
% 1.44/0.56  % (29677)Refutation not found, incomplete strategy% (29677)------------------------------
% 1.44/0.56  % (29677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (29677)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (29677)Memory used [KB]: 1663
% 1.44/0.56  % (29677)Time elapsed: 0.150 s
% 1.44/0.56  % (29677)------------------------------
% 1.44/0.56  % (29677)------------------------------
% 1.44/0.56  % (29666)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_11 on theBenchmark
% 1.44/0.56  % (29680)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_157 on theBenchmark
% 1.44/0.56  % (29666)Refutation not found, incomplete strategy% (29666)------------------------------
% 1.44/0.56  % (29666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (29666)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (29666)Memory used [KB]: 6140
% 1.44/0.56  % (29666)Time elapsed: 0.147 s
% 1.44/0.56  % (29666)------------------------------
% 1.44/0.56  % (29666)------------------------------
% 1.44/0.56  % (29684)Refutation not found, incomplete strategy% (29684)------------------------------
% 1.44/0.56  % (29684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (29684)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (29684)Memory used [KB]: 10746
% 1.44/0.56  % (29684)Time elapsed: 0.148 s
% 1.44/0.56  % (29684)------------------------------
% 1.44/0.56  % (29684)------------------------------
% 1.44/0.56  % (29686)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_4 on theBenchmark
% 1.57/0.57  % (29667)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_6 on theBenchmark
% 1.57/0.58  % (29669)Refutation found. Thanks to Tanya!
% 1.57/0.58  % SZS status Theorem for theBenchmark
% 1.57/0.58  % SZS output start Proof for theBenchmark
% 1.57/0.58  fof(f426,plain,(
% 1.57/0.58    $false),
% 1.57/0.58    inference(avatar_sat_refutation,[],[f65,f86,f88,f271,f321,f341,f403,f420,f425])).
% 1.57/0.58  fof(f425,plain,(
% 1.57/0.58    spl7_1 | ~spl7_8),
% 1.57/0.58    inference(avatar_contradiction_clause,[],[f424])).
% 1.57/0.58  fof(f424,plain,(
% 1.57/0.58    $false | (spl7_1 | ~spl7_8)),
% 1.57/0.58    inference(subsumption_resolution,[],[f423,f60])).
% 1.57/0.58  fof(f60,plain,(
% 1.57/0.58    ~r1_tarski(sK0,sK2) | spl7_1),
% 1.57/0.58    inference(avatar_component_clause,[],[f58])).
% 1.57/0.58  fof(f58,plain,(
% 1.57/0.58    spl7_1 <=> r1_tarski(sK0,sK2)),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.57/0.58  fof(f423,plain,(
% 1.57/0.58    r1_tarski(sK0,sK2) | ~spl7_8),
% 1.57/0.58    inference(duplicate_literal_removal,[],[f421])).
% 1.57/0.58  fof(f421,plain,(
% 1.57/0.58    r1_tarski(sK0,sK2) | r1_tarski(sK0,sK2) | ~spl7_8),
% 1.57/0.58    inference(resolution,[],[f363,f46])).
% 1.57/0.58  fof(f46,plain,(
% 1.57/0.58    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f28])).
% 1.57/0.58  fof(f28,plain,(
% 1.57/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.57/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f26,f27])).
% 1.57/0.58  fof(f27,plain,(
% 1.57/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.57/0.58    introduced(choice_axiom,[])).
% 1.57/0.58  fof(f26,plain,(
% 1.57/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.57/0.58    inference(rectify,[],[f25])).
% 1.57/0.58  fof(f25,plain,(
% 1.57/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.57/0.58    inference(nnf_transformation,[],[f17])).
% 1.57/0.58  fof(f17,plain,(
% 1.57/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.57/0.58    inference(ennf_transformation,[],[f1])).
% 1.57/0.58  fof(f1,axiom,(
% 1.57/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.57/0.58  fof(f363,plain,(
% 1.57/0.58    ( ! [X9] : (r2_hidden(sK6(sK0,X9),sK2) | r1_tarski(sK0,X9)) ) | ~spl7_8),
% 1.57/0.58    inference(resolution,[],[f251,f45])).
% 1.57/0.58  fof(f45,plain,(
% 1.57/0.58    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f28])).
% 1.57/0.58  fof(f251,plain,(
% 1.57/0.58    ( ! [X2] : (~r2_hidden(X2,sK0) | r2_hidden(X2,sK2)) ) | ~spl7_8),
% 1.57/0.58    inference(avatar_component_clause,[],[f250])).
% 1.57/0.58  fof(f250,plain,(
% 1.57/0.58    spl7_8 <=> ! [X2] : (~r2_hidden(X2,sK0) | r2_hidden(X2,sK2))),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.57/0.58  fof(f420,plain,(
% 1.57/0.58    spl7_2 | ~spl7_5),
% 1.57/0.58    inference(avatar_contradiction_clause,[],[f419])).
% 1.57/0.58  fof(f419,plain,(
% 1.57/0.58    $false | (spl7_2 | ~spl7_5)),
% 1.57/0.58    inference(subsumption_resolution,[],[f418,f64])).
% 1.57/0.58  fof(f64,plain,(
% 1.57/0.58    ~r1_tarski(sK1,sK3) | spl7_2),
% 1.57/0.58    inference(avatar_component_clause,[],[f62])).
% 1.57/0.58  fof(f62,plain,(
% 1.57/0.58    spl7_2 <=> r1_tarski(sK1,sK3)),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.57/0.58  fof(f418,plain,(
% 1.57/0.58    r1_tarski(sK1,sK3) | ~spl7_5),
% 1.57/0.58    inference(duplicate_literal_removal,[],[f416])).
% 1.57/0.58  fof(f416,plain,(
% 1.57/0.58    r1_tarski(sK1,sK3) | r1_tarski(sK1,sK3) | ~spl7_5),
% 1.57/0.58    inference(resolution,[],[f352,f46])).
% 1.57/0.58  fof(f352,plain,(
% 1.57/0.58    ( ! [X9] : (r2_hidden(sK6(sK1,X9),sK3) | r1_tarski(sK1,X9)) ) | ~spl7_5),
% 1.57/0.58    inference(resolution,[],[f241,f45])).
% 1.57/0.58  fof(f241,plain,(
% 1.57/0.58    ( ! [X1] : (~r2_hidden(X1,sK1) | r2_hidden(X1,sK3)) ) | ~spl7_5),
% 1.57/0.58    inference(avatar_component_clause,[],[f240])).
% 1.57/0.58  fof(f240,plain,(
% 1.57/0.58    spl7_5 <=> ! [X1] : (~r2_hidden(X1,sK1) | r2_hidden(X1,sK3))),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.57/0.58  fof(f403,plain,(
% 1.57/0.58    spl7_7 | spl7_8),
% 1.57/0.58    inference(avatar_split_clause,[],[f401,f250,f247])).
% 1.57/0.58  fof(f247,plain,(
% 1.57/0.58    spl7_7 <=> ! [X3] : ~r2_hidden(X3,sK1)),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.57/0.58  fof(f401,plain,(
% 1.57/0.58    ( ! [X2,X3] : (~r2_hidden(X2,sK0) | ~r2_hidden(X3,sK1) | r2_hidden(X2,sK2)) )),
% 1.57/0.58    inference(resolution,[],[f182,f50])).
% 1.57/0.58  fof(f50,plain,(
% 1.57/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f32])).
% 1.57/0.58  fof(f32,plain,(
% 1.57/0.58    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.57/0.58    inference(flattening,[],[f31])).
% 1.57/0.58  fof(f31,plain,(
% 1.57/0.58    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.57/0.58    inference(nnf_transformation,[],[f8])).
% 1.57/0.58  fof(f8,axiom,(
% 1.57/0.58    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.57/0.58  fof(f182,plain,(
% 1.57/0.58    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3)) | ~r2_hidden(X0,sK0) | ~r2_hidden(X1,sK1)) )),
% 1.57/0.58    inference(resolution,[],[f114,f33])).
% 1.57/0.58  fof(f33,plain,(
% 1.57/0.58    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 1.57/0.58    inference(cnf_transformation,[],[f19])).
% 1.57/0.58  fof(f19,plain,(
% 1.57/0.58    (~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 1.57/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f18])).
% 1.57/0.58  fof(f18,plain,(
% 1.57/0.58    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),
% 1.57/0.58    introduced(choice_axiom,[])).
% 1.57/0.58  fof(f14,plain,(
% 1.57/0.58    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.57/0.58    inference(flattening,[],[f13])).
% 1.57/0.58  fof(f13,plain,(
% 1.57/0.58    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.57/0.58    inference(ennf_transformation,[],[f11])).
% 1.57/0.58  fof(f11,negated_conjecture,(
% 1.57/0.58    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.57/0.58    inference(negated_conjecture,[],[f10])).
% 1.57/0.58  fof(f10,conjecture,(
% 1.57/0.58    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 1.57/0.58  fof(f114,plain,(
% 1.57/0.58    ( ! [X12,X10,X8,X11,X9] : (~r1_tarski(k2_zfmisc_1(X11,X9),X12) | ~r2_hidden(X10,X11) | r2_hidden(k4_tarski(X10,X8),X12) | ~r2_hidden(X8,X9)) )),
% 1.57/0.58    inference(resolution,[],[f52,f44])).
% 1.57/0.58  fof(f44,plain,(
% 1.57/0.58    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f28])).
% 1.57/0.58  fof(f52,plain,(
% 1.57/0.58    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f32])).
% 1.57/0.58  fof(f341,plain,(
% 1.57/0.58    spl7_5 | spl7_6),
% 1.57/0.58    inference(avatar_split_clause,[],[f338,f243,f240])).
% 1.57/0.58  fof(f243,plain,(
% 1.57/0.58    spl7_6 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.57/0.58  fof(f338,plain,(
% 1.57/0.58    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X1,sK1) | r2_hidden(X1,sK3)) )),
% 1.57/0.58    inference(resolution,[],[f182,f51])).
% 1.57/0.58  fof(f51,plain,(
% 1.57/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f32])).
% 1.57/0.58  fof(f321,plain,(
% 1.57/0.58    ~spl7_4 | ~spl7_6),
% 1.57/0.58    inference(avatar_contradiction_clause,[],[f320])).
% 1.57/0.58  fof(f320,plain,(
% 1.57/0.58    $false | (~spl7_4 | ~spl7_6)),
% 1.57/0.58    inference(subsumption_resolution,[],[f317,f56])).
% 1.57/0.58  fof(f56,plain,(
% 1.57/0.58    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.57/0.58    inference(equality_resolution,[],[f48])).
% 1.57/0.58  fof(f48,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.57/0.58    inference(cnf_transformation,[],[f30])).
% 1.57/0.58  fof(f30,plain,(
% 1.57/0.58    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.57/0.58    inference(flattening,[],[f29])).
% 1.57/0.58  fof(f29,plain,(
% 1.57/0.58    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.57/0.58    inference(nnf_transformation,[],[f9])).
% 1.57/0.58  fof(f9,axiom,(
% 1.57/0.58    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.57/0.58  fof(f317,plain,(
% 1.57/0.58    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | (~spl7_4 | ~spl7_6)),
% 1.57/0.58    inference(backward_demodulation,[],[f34,f308])).
% 1.57/0.58  fof(f308,plain,(
% 1.57/0.58    k1_xboole_0 = sK0 | (~spl7_4 | ~spl7_6)),
% 1.57/0.58    inference(resolution,[],[f244,f101])).
% 1.57/0.58  fof(f101,plain,(
% 1.57/0.58    ( ! [X3] : (r2_hidden(sK5(X3,k1_xboole_0),X3) | k1_xboole_0 = X3) ) | ~spl7_4),
% 1.57/0.58    inference(resolution,[],[f42,f83])).
% 1.57/0.58  fof(f83,plain,(
% 1.57/0.58    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl7_4),
% 1.57/0.58    inference(avatar_component_clause,[],[f82])).
% 1.57/0.58  fof(f82,plain,(
% 1.57/0.58    spl7_4 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.57/0.58  fof(f42,plain,(
% 1.57/0.58    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | X0 = X1 | r2_hidden(sK5(X0,X1),X0)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f24])).
% 1.57/0.58  fof(f24,plain,(
% 1.57/0.58    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK5(X0,X1),X1) | ~r2_hidden(sK5(X0,X1),X0)) & (r2_hidden(sK5(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0))))),
% 1.57/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).
% 1.57/0.58  fof(f23,plain,(
% 1.57/0.58    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK5(X0,X1),X1) | ~r2_hidden(sK5(X0,X1),X0)) & (r2_hidden(sK5(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0))))),
% 1.57/0.58    introduced(choice_axiom,[])).
% 1.57/0.58  fof(f22,plain,(
% 1.57/0.58    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.57/0.58    inference(nnf_transformation,[],[f16])).
% 1.57/0.58  fof(f16,plain,(
% 1.57/0.58    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.57/0.58    inference(ennf_transformation,[],[f2])).
% 1.57/0.58  fof(f2,axiom,(
% 1.57/0.58    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 1.57/0.58  fof(f244,plain,(
% 1.57/0.58    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl7_6),
% 1.57/0.58    inference(avatar_component_clause,[],[f243])).
% 1.57/0.58  fof(f34,plain,(
% 1.57/0.58    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.57/0.58    inference(cnf_transformation,[],[f19])).
% 1.57/0.58  fof(f271,plain,(
% 1.57/0.58    ~spl7_4 | ~spl7_7),
% 1.57/0.58    inference(avatar_contradiction_clause,[],[f270])).
% 1.57/0.58  fof(f270,plain,(
% 1.57/0.58    $false | (~spl7_4 | ~spl7_7)),
% 1.57/0.58    inference(subsumption_resolution,[],[f267,f55])).
% 1.57/0.58  fof(f55,plain,(
% 1.57/0.58    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.57/0.58    inference(equality_resolution,[],[f49])).
% 1.57/0.58  fof(f49,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.57/0.58    inference(cnf_transformation,[],[f30])).
% 1.57/0.58  fof(f267,plain,(
% 1.57/0.58    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | (~spl7_4 | ~spl7_7)),
% 1.57/0.58    inference(backward_demodulation,[],[f34,f257])).
% 1.57/0.58  fof(f257,plain,(
% 1.57/0.58    k1_xboole_0 = sK1 | (~spl7_4 | ~spl7_7)),
% 1.57/0.58    inference(resolution,[],[f248,f101])).
% 1.57/0.58  fof(f248,plain,(
% 1.57/0.58    ( ! [X3] : (~r2_hidden(X3,sK1)) ) | ~spl7_7),
% 1.57/0.58    inference(avatar_component_clause,[],[f247])).
% 1.57/0.58  fof(f88,plain,(
% 1.57/0.58    ~spl7_3),
% 1.57/0.58    inference(avatar_contradiction_clause,[],[f87])).
% 1.57/0.58  fof(f87,plain,(
% 1.57/0.58    $false | ~spl7_3),
% 1.57/0.58    inference(resolution,[],[f80,f36])).
% 1.57/0.58  fof(f36,plain,(
% 1.57/0.58    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f7])).
% 1.57/0.58  fof(f7,axiom,(
% 1.57/0.58    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.57/0.58  fof(f80,plain,(
% 1.57/0.58    ( ! [X0] : (~r1_xboole_0(k1_xboole_0,X0)) ) | ~spl7_3),
% 1.57/0.58    inference(avatar_component_clause,[],[f79])).
% 1.57/0.58  fof(f79,plain,(
% 1.57/0.58    spl7_3 <=> ! [X0] : ~r1_xboole_0(k1_xboole_0,X0)),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.57/0.58  fof(f86,plain,(
% 1.57/0.58    spl7_3 | spl7_4),
% 1.57/0.58    inference(avatar_split_clause,[],[f76,f82,f79])).
% 1.57/0.58  fof(f76,plain,(
% 1.57/0.58    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,X0)) )),
% 1.57/0.58    inference(superposition,[],[f53,f37])).
% 1.57/0.58  fof(f37,plain,(
% 1.57/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f6])).
% 1.57/0.58  fof(f6,axiom,(
% 1.57/0.58    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.57/0.58  fof(f53,plain,(
% 1.57/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.57/0.58    inference(definition_unfolding,[],[f41,f39])).
% 1.57/0.58  fof(f39,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.57/0.58    inference(cnf_transformation,[],[f5])).
% 1.57/0.58  fof(f5,axiom,(
% 1.57/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.57/0.58  fof(f41,plain,(
% 1.57/0.58    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.57/0.58    inference(cnf_transformation,[],[f21])).
% 1.57/0.58  fof(f21,plain,(
% 1.57/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.57/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f20])).
% 1.57/0.58  fof(f20,plain,(
% 1.57/0.58    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.57/0.58    introduced(choice_axiom,[])).
% 1.57/0.58  fof(f15,plain,(
% 1.57/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.57/0.58    inference(ennf_transformation,[],[f12])).
% 1.57/0.58  fof(f12,plain,(
% 1.57/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.57/0.58    inference(rectify,[],[f3])).
% 1.57/0.58  fof(f3,axiom,(
% 1.57/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.57/0.58  fof(f65,plain,(
% 1.57/0.58    ~spl7_1 | ~spl7_2),
% 1.57/0.58    inference(avatar_split_clause,[],[f35,f62,f58])).
% 1.57/0.58  fof(f35,plain,(
% 1.57/0.58    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 1.57/0.58    inference(cnf_transformation,[],[f19])).
% 1.57/0.58  % SZS output end Proof for theBenchmark
% 1.57/0.58  % (29669)------------------------------
% 1.57/0.58  % (29669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.58  % (29669)Termination reason: Refutation
% 1.57/0.58  
% 1.57/0.58  % (29669)Memory used [KB]: 6396
% 1.57/0.58  % (29669)Time elapsed: 0.151 s
% 1.57/0.58  % (29669)------------------------------
% 1.57/0.58  % (29669)------------------------------
% 1.57/0.60  % (29657)Success in time 0.234 s
%------------------------------------------------------------------------------
