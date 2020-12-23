%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:38 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 284 expanded)
%              Number of leaves         :   29 ( 100 expanded)
%              Depth                    :   12
%              Number of atoms          :  348 (1105 expanded)
%              Number of equality atoms :   52 ( 207 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f289,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f73,f78,f83,f169,f175,f192,f202,f205,f224,f242,f252,f260,f268,f282,f287,f288])).

fof(f288,plain,
    ( sK0 != k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ r1_tarski(sK1,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | r1_tarski(sK1,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f287,plain,(
    spl4_22 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | spl4_22 ),
    inference(unit_resulting_resolution,[],[f52,f277])).

fof(f277,plain,
    ( ~ r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl4_22
  <=> r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f30,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f282,plain,
    ( ~ spl4_22
    | spl4_23
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f270,f265,f279,f275])).

fof(f279,plain,
    ( spl4_23
  <=> sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f265,plain,
    ( spl4_21
  <=> r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f270,plain,
    ( sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | ~ spl4_21 ),
    inference(resolution,[],[f267,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f267,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK0)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f265])).

fof(f268,plain,
    ( spl4_21
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f263,f221,f265])).

fof(f221,plain,
    ( spl4_20
  <=> r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f263,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK0)
    | ~ spl4_20 ),
    inference(resolution,[],[f223,f58])).

fof(f58,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f223,plain,
    ( r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f221])).

fof(f260,plain,(
    ~ spl4_19 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | ~ spl4_19 ),
    inference(unit_resulting_resolution,[],[f52,f219,f57])).

fof(f57,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f219,plain,
    ( ! [X0] : ~ r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),X0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl4_19
  <=> ! [X0] : ~ r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f252,plain,(
    ~ spl4_17 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | ~ spl4_17 ),
    inference(unit_resulting_resolution,[],[f52,f197,f57])).

fof(f197,plain,
    ( ! [X1] : ~ r2_hidden(sK1,X1)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl4_17
  <=> ! [X1] : ~ r2_hidden(sK1,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f242,plain,
    ( spl4_2
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f241,f189,f70])).

fof(f70,plain,
    ( spl4_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f189,plain,
    ( spl4_16
  <=> sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f241,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_16 ),
    inference(superposition,[],[f52,f191])).

fof(f191,plain,
    ( sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f189])).

fof(f224,plain,
    ( spl4_19
    | spl4_20
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f216,f167,f221,f218])).

fof(f167,plain,
    ( spl4_13
  <=> ! [X1] : ~ r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k4_xboole_0(X1,k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f216,plain,
    ( ! [X0] :
        ( r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK0))
        | ~ r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),X0) )
    | ~ spl4_13 ),
    inference(resolution,[],[f168,f59])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f168,plain,
    ( ! [X1] : ~ r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k4_xboole_0(X1,k1_zfmisc_1(sK0)))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f167])).

fof(f205,plain,(
    spl4_18 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl4_18 ),
    inference(unit_resulting_resolution,[],[f56,f201,f57])).

fof(f201,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK1))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl4_18
  <=> r2_hidden(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f202,plain,
    ( spl4_17
    | ~ spl4_18
    | ~ spl4_4
    | spl4_15 ),
    inference(avatar_split_clause,[],[f194,f185,f80,f199,f196])).

fof(f80,plain,
    ( spl4_4
  <=> k3_tarski(k1_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))) = k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f185,plain,
    ( spl4_15
  <=> r1_tarski(sK1,k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f194,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK1,k1_zfmisc_1(sK1))
        | ~ r2_hidden(sK1,X1) )
    | ~ spl4_4
    | spl4_15 ),
    inference(resolution,[],[f187,f153])).

fof(f153,plain,
    ( ! [X4,X3] :
        ( r1_tarski(X3,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
        | ~ r2_hidden(X3,k1_zfmisc_1(sK1))
        | ~ r2_hidden(X3,X4) )
    | ~ spl4_4 ),
    inference(resolution,[],[f124,f58])).

fof(f124,plain,
    ( ! [X6,X7] :
        ( r2_hidden(X6,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))
        | ~ r2_hidden(X6,X7)
        | ~ r2_hidden(X6,k1_zfmisc_1(sK1)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f94,f60])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f94,plain,
    ( ! [X4,X5] :
        ( r2_hidden(X5,k4_xboole_0(k4_xboole_0(X4,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK1)))
        | r2_hidden(X5,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))
        | ~ r2_hidden(X5,X4) )
    | ~ spl4_4 ),
    inference(superposition,[],[f59,f84])).

fof(f84,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(X0,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK1)) = k4_xboole_0(X0,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))
    | ~ spl4_4 ),
    inference(superposition,[],[f54,f82])).

fof(f82,plain,
    ( k3_tarski(k1_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))) = k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f54,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(definition_unfolding,[],[f43,f50])).

fof(f43,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f187,plain,
    ( ~ r1_tarski(sK1,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f185])).

fof(f192,plain,
    ( ~ spl4_15
    | spl4_16
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f176,f172,f189,f185])).

fof(f172,plain,
    ( spl4_14
  <=> r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f176,plain,
    ( sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ r1_tarski(sK1,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | ~ spl4_14 ),
    inference(resolution,[],[f174,f36])).

fof(f174,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK1)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f172])).

fof(f175,plain,
    ( spl4_14
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f170,f163,f172])).

fof(f163,plain,
    ( spl4_12
  <=> r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f170,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK1)
    | ~ spl4_12 ),
    inference(resolution,[],[f165,f58])).

fof(f165,plain,
    ( r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f163])).

fof(f169,plain,
    ( spl4_12
    | spl4_13
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f118,f80,f167,f163])).

fof(f118,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k4_xboole_0(X1,k1_zfmisc_1(sK0)))
        | r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK1)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f112,f56])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_zfmisc_1(sK0)))
        | r2_hidden(X0,k1_zfmisc_1(sK1)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f99,f57])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))
        | r2_hidden(X0,k1_zfmisc_1(sK1))
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_zfmisc_1(sK0))) )
    | ~ spl4_4 ),
    inference(resolution,[],[f93,f59])).

fof(f93,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k4_xboole_0(k4_xboole_0(X2,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK1)))
        | ~ r2_hidden(X3,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))) )
    | ~ spl4_4 ),
    inference(superposition,[],[f60,f84])).

fof(f83,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f51,f80])).

fof(f51,plain,(
    k3_tarski(k1_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))) = k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f28,f50,f50])).

fof(f28,plain,(
    k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    & k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ~ r3_xboole_0(X0,X1)
        & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) )
   => ( ~ r3_xboole_0(sK0,sK1)
      & k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ~ r3_xboole_0(X0,X1)
      & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1))
       => r3_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1))
     => r3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_zfmisc_1)).

fof(f78,plain,
    ( ~ spl4_3
    | spl4_1 ),
    inference(avatar_split_clause,[],[f68,f63,f75])).

fof(f75,plain,
    ( spl4_3
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f63,plain,
    ( spl4_1
  <=> r3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f68,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl4_1 ),
    inference(resolution,[],[f65,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ( ~ r1_tarski(X1,X0)
        & ~ r1_tarski(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) )
     => r3_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).

fof(f65,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f73,plain,
    ( ~ spl4_2
    | spl4_1 ),
    inference(avatar_split_clause,[],[f67,f63,f70])).

fof(f67,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl4_1 ),
    inference(resolution,[],[f65,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f66,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f29,f63])).

fof(f29,plain,(
    ~ r3_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:11:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (22278)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.49  % (22270)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.50  % (22295)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (22286)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.51  % (22287)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.51  % (22287)Refutation not found, incomplete strategy% (22287)------------------------------
% 0.21/0.51  % (22287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22287)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22287)Memory used [KB]: 1663
% 0.21/0.51  % (22287)Time elapsed: 0.111 s
% 0.21/0.51  % (22287)------------------------------
% 0.21/0.51  % (22287)------------------------------
% 0.21/0.51  % (22273)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (22291)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (22284)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (22283)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (22283)Refutation not found, incomplete strategy% (22283)------------------------------
% 0.21/0.53  % (22283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22283)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (22283)Memory used [KB]: 1663
% 0.21/0.53  % (22283)Time elapsed: 0.092 s
% 0.21/0.53  % (22283)------------------------------
% 0.21/0.53  % (22283)------------------------------
% 0.21/0.53  % (22298)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (22296)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (22298)Refutation not found, incomplete strategy% (22298)------------------------------
% 0.21/0.53  % (22298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22274)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (22277)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (22271)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (22276)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (22297)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (22272)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (22279)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (22290)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (22288)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (22282)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (22281)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (22280)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (22293)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (22294)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (22289)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (22275)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (22285)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (22298)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22298)Memory used [KB]: 1663
% 0.21/0.55  % (22298)Time elapsed: 0.129 s
% 0.21/0.55  % (22298)------------------------------
% 0.21/0.55  % (22298)------------------------------
% 0.21/0.55  % (22292)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (22285)Refutation not found, incomplete strategy% (22285)------------------------------
% 0.21/0.55  % (22285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22285)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22285)Memory used [KB]: 10618
% 0.21/0.55  % (22285)Time elapsed: 0.148 s
% 0.21/0.55  % (22285)------------------------------
% 0.21/0.55  % (22285)------------------------------
% 0.21/0.55  % (22269)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.51/0.55  % (22296)Refutation not found, incomplete strategy% (22296)------------------------------
% 1.51/0.55  % (22296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.55  % (22296)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.55  
% 1.51/0.55  % (22296)Memory used [KB]: 6268
% 1.51/0.55  % (22296)Time elapsed: 0.158 s
% 1.51/0.55  % (22296)------------------------------
% 1.51/0.55  % (22296)------------------------------
% 1.51/0.57  % (22279)Refutation found. Thanks to Tanya!
% 1.51/0.57  % SZS status Theorem for theBenchmark
% 1.51/0.57  % SZS output start Proof for theBenchmark
% 1.51/0.57  fof(f289,plain,(
% 1.51/0.57    $false),
% 1.51/0.57    inference(avatar_sat_refutation,[],[f66,f73,f78,f83,f169,f175,f192,f202,f205,f224,f242,f252,f260,f268,f282,f287,f288])).
% 1.51/0.57  fof(f288,plain,(
% 1.51/0.57    sK0 != k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~r1_tarski(sK1,k3_tarski(k1_enumset1(sK0,sK0,sK1))) | r1_tarski(sK1,sK0)),
% 1.51/0.57    introduced(theory_tautology_sat_conflict,[])).
% 1.51/0.57  fof(f287,plain,(
% 1.51/0.57    spl4_22),
% 1.51/0.57    inference(avatar_contradiction_clause,[],[f283])).
% 1.51/0.57  fof(f283,plain,(
% 1.51/0.57    $false | spl4_22),
% 1.51/0.57    inference(unit_resulting_resolution,[],[f52,f277])).
% 1.51/0.57  fof(f277,plain,(
% 1.51/0.57    ~r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1))) | spl4_22),
% 1.51/0.57    inference(avatar_component_clause,[],[f275])).
% 1.51/0.57  fof(f275,plain,(
% 1.51/0.57    spl4_22 <=> r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1)))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.51/0.57  fof(f52,plain,(
% 1.51/0.57    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 1.51/0.57    inference(definition_unfolding,[],[f30,f50])).
% 1.51/0.57  fof(f50,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.51/0.57    inference(definition_unfolding,[],[f32,f33])).
% 1.51/0.57  fof(f33,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f7])).
% 1.51/0.57  fof(f7,axiom,(
% 1.51/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.51/0.57  fof(f32,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.51/0.57    inference(cnf_transformation,[],[f9])).
% 1.51/0.57  fof(f9,axiom,(
% 1.51/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.51/0.57  fof(f30,plain,(
% 1.51/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.51/0.57    inference(cnf_transformation,[],[f6])).
% 1.51/0.57  fof(f6,axiom,(
% 1.51/0.57    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.51/0.57  fof(f282,plain,(
% 1.51/0.57    ~spl4_22 | spl4_23 | ~spl4_21),
% 1.51/0.57    inference(avatar_split_clause,[],[f270,f265,f279,f275])).
% 1.51/0.57  fof(f279,plain,(
% 1.51/0.57    spl4_23 <=> sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.51/0.57  fof(f265,plain,(
% 1.51/0.57    spl4_21 <=> r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK0)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.51/0.57  fof(f270,plain,(
% 1.51/0.57    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1))) | ~spl4_21),
% 1.51/0.57    inference(resolution,[],[f267,f36])).
% 1.51/0.57  fof(f36,plain,(
% 1.51/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f18])).
% 1.51/0.57  fof(f18,plain,(
% 1.51/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.51/0.57    inference(flattening,[],[f17])).
% 1.51/0.57  fof(f17,plain,(
% 1.51/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.51/0.57    inference(nnf_transformation,[],[f3])).
% 1.51/0.57  fof(f3,axiom,(
% 1.51/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.51/0.57  fof(f267,plain,(
% 1.51/0.57    r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK0) | ~spl4_21),
% 1.51/0.57    inference(avatar_component_clause,[],[f265])).
% 1.51/0.57  fof(f268,plain,(
% 1.51/0.57    spl4_21 | ~spl4_20),
% 1.51/0.57    inference(avatar_split_clause,[],[f263,f221,f265])).
% 1.51/0.57  fof(f221,plain,(
% 1.51/0.57    spl4_20 <=> r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK0))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.51/0.57  fof(f263,plain,(
% 1.51/0.57    r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK0) | ~spl4_20),
% 1.51/0.57    inference(resolution,[],[f223,f58])).
% 1.51/0.57  fof(f58,plain,(
% 1.51/0.57    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.51/0.57    inference(equality_resolution,[],[f39])).
% 1.51/0.57  fof(f39,plain,(
% 1.51/0.57    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.51/0.57    inference(cnf_transformation,[],[f22])).
% 1.51/0.57  fof(f22,plain,(
% 1.51/0.57    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.51/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).
% 1.51/0.57  fof(f21,plain,(
% 1.51/0.57    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.51/0.57    introduced(choice_axiom,[])).
% 1.51/0.57  fof(f20,plain,(
% 1.51/0.57    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.51/0.57    inference(rectify,[],[f19])).
% 1.51/0.57  fof(f19,plain,(
% 1.51/0.57    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.51/0.57    inference(nnf_transformation,[],[f8])).
% 1.51/0.57  fof(f8,axiom,(
% 1.51/0.57    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.51/0.57  fof(f223,plain,(
% 1.51/0.57    r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK0)) | ~spl4_20),
% 1.51/0.57    inference(avatar_component_clause,[],[f221])).
% 1.51/0.57  fof(f260,plain,(
% 1.51/0.57    ~spl4_19),
% 1.51/0.57    inference(avatar_contradiction_clause,[],[f257])).
% 1.51/0.57  fof(f257,plain,(
% 1.51/0.57    $false | ~spl4_19),
% 1.51/0.57    inference(unit_resulting_resolution,[],[f52,f219,f57])).
% 1.51/0.57  fof(f57,plain,(
% 1.51/0.57    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.51/0.57    inference(equality_resolution,[],[f40])).
% 1.51/0.57  fof(f40,plain,(
% 1.51/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.51/0.57    inference(cnf_transformation,[],[f22])).
% 1.51/0.57  fof(f219,plain,(
% 1.51/0.57    ( ! [X0] : (~r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),X0)) ) | ~spl4_19),
% 1.51/0.57    inference(avatar_component_clause,[],[f218])).
% 1.51/0.57  fof(f218,plain,(
% 1.51/0.57    spl4_19 <=> ! [X0] : ~r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),X0)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.51/0.57  fof(f252,plain,(
% 1.51/0.57    ~spl4_17),
% 1.51/0.57    inference(avatar_contradiction_clause,[],[f244])).
% 1.51/0.57  fof(f244,plain,(
% 1.51/0.57    $false | ~spl4_17),
% 1.51/0.57    inference(unit_resulting_resolution,[],[f52,f197,f57])).
% 1.51/0.57  fof(f197,plain,(
% 1.51/0.57    ( ! [X1] : (~r2_hidden(sK1,X1)) ) | ~spl4_17),
% 1.51/0.57    inference(avatar_component_clause,[],[f196])).
% 1.51/0.57  fof(f196,plain,(
% 1.51/0.57    spl4_17 <=> ! [X1] : ~r2_hidden(sK1,X1)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.51/0.57  fof(f242,plain,(
% 1.51/0.57    spl4_2 | ~spl4_16),
% 1.51/0.57    inference(avatar_split_clause,[],[f241,f189,f70])).
% 1.51/0.57  fof(f70,plain,(
% 1.51/0.57    spl4_2 <=> r1_tarski(sK0,sK1)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.51/0.57  fof(f189,plain,(
% 1.51/0.57    spl4_16 <=> sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.51/0.57  fof(f241,plain,(
% 1.51/0.57    r1_tarski(sK0,sK1) | ~spl4_16),
% 1.51/0.57    inference(superposition,[],[f52,f191])).
% 1.51/0.57  fof(f191,plain,(
% 1.51/0.57    sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~spl4_16),
% 1.51/0.57    inference(avatar_component_clause,[],[f189])).
% 1.51/0.57  fof(f224,plain,(
% 1.51/0.57    spl4_19 | spl4_20 | ~spl4_13),
% 1.51/0.57    inference(avatar_split_clause,[],[f216,f167,f221,f218])).
% 1.51/0.57  fof(f167,plain,(
% 1.51/0.57    spl4_13 <=> ! [X1] : ~r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k4_xboole_0(X1,k1_zfmisc_1(sK0)))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.51/0.57  fof(f216,plain,(
% 1.51/0.57    ( ! [X0] : (r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK0)) | ~r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),X0)) ) | ~spl4_13),
% 1.51/0.57    inference(resolution,[],[f168,f59])).
% 1.51/0.57  fof(f59,plain,(
% 1.51/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.51/0.57    inference(equality_resolution,[],[f46])).
% 1.51/0.57  fof(f46,plain,(
% 1.51/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.51/0.57    inference(cnf_transformation,[],[f27])).
% 1.51/0.57  fof(f27,plain,(
% 1.51/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.51/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).
% 1.51/0.57  fof(f26,plain,(
% 1.51/0.57    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.51/0.57    introduced(choice_axiom,[])).
% 1.51/0.57  fof(f25,plain,(
% 1.51/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.51/0.57    inference(rectify,[],[f24])).
% 1.51/0.57  fof(f24,plain,(
% 1.51/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.51/0.57    inference(flattening,[],[f23])).
% 1.51/0.57  fof(f23,plain,(
% 1.51/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.51/0.57    inference(nnf_transformation,[],[f2])).
% 1.51/0.57  fof(f2,axiom,(
% 1.51/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.51/0.57  fof(f168,plain,(
% 1.51/0.57    ( ! [X1] : (~r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k4_xboole_0(X1,k1_zfmisc_1(sK0)))) ) | ~spl4_13),
% 1.51/0.57    inference(avatar_component_clause,[],[f167])).
% 1.51/0.57  fof(f205,plain,(
% 1.51/0.57    spl4_18),
% 1.51/0.57    inference(avatar_contradiction_clause,[],[f203])).
% 1.51/0.57  fof(f203,plain,(
% 1.51/0.57    $false | spl4_18),
% 1.51/0.57    inference(unit_resulting_resolution,[],[f56,f201,f57])).
% 1.51/0.57  fof(f201,plain,(
% 1.51/0.57    ~r2_hidden(sK1,k1_zfmisc_1(sK1)) | spl4_18),
% 1.51/0.57    inference(avatar_component_clause,[],[f199])).
% 1.51/0.57  fof(f199,plain,(
% 1.51/0.57    spl4_18 <=> r2_hidden(sK1,k1_zfmisc_1(sK1))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.51/0.57  fof(f56,plain,(
% 1.51/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.51/0.57    inference(equality_resolution,[],[f34])).
% 1.51/0.57  fof(f34,plain,(
% 1.51/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.51/0.57    inference(cnf_transformation,[],[f18])).
% 1.51/0.57  fof(f202,plain,(
% 1.51/0.57    spl4_17 | ~spl4_18 | ~spl4_4 | spl4_15),
% 1.51/0.57    inference(avatar_split_clause,[],[f194,f185,f80,f199,f196])).
% 1.51/0.57  fof(f80,plain,(
% 1.51/0.57    spl4_4 <=> k3_tarski(k1_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))) = k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.51/0.57  fof(f185,plain,(
% 1.51/0.57    spl4_15 <=> r1_tarski(sK1,k3_tarski(k1_enumset1(sK0,sK0,sK1)))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.51/0.57  fof(f194,plain,(
% 1.51/0.57    ( ! [X1] : (~r2_hidden(sK1,k1_zfmisc_1(sK1)) | ~r2_hidden(sK1,X1)) ) | (~spl4_4 | spl4_15)),
% 1.51/0.57    inference(resolution,[],[f187,f153])).
% 1.51/0.57  fof(f153,plain,(
% 1.51/0.57    ( ! [X4,X3] : (r1_tarski(X3,k3_tarski(k1_enumset1(sK0,sK0,sK1))) | ~r2_hidden(X3,k1_zfmisc_1(sK1)) | ~r2_hidden(X3,X4)) ) | ~spl4_4),
% 1.51/0.57    inference(resolution,[],[f124,f58])).
% 1.51/0.57  fof(f124,plain,(
% 1.51/0.57    ( ! [X6,X7] : (r2_hidden(X6,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))) | ~r2_hidden(X6,X7) | ~r2_hidden(X6,k1_zfmisc_1(sK1))) ) | ~spl4_4),
% 1.51/0.57    inference(resolution,[],[f94,f60])).
% 1.51/0.57  fof(f60,plain,(
% 1.51/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.51/0.57    inference(equality_resolution,[],[f45])).
% 1.51/0.57  fof(f45,plain,(
% 1.51/0.57    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.51/0.57    inference(cnf_transformation,[],[f27])).
% 1.51/0.57  fof(f94,plain,(
% 1.51/0.57    ( ! [X4,X5] : (r2_hidden(X5,k4_xboole_0(k4_xboole_0(X4,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK1))) | r2_hidden(X5,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))) | ~r2_hidden(X5,X4)) ) | ~spl4_4),
% 1.51/0.57    inference(superposition,[],[f59,f84])).
% 1.51/0.57  fof(f84,plain,(
% 1.51/0.57    ( ! [X0] : (k4_xboole_0(k4_xboole_0(X0,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK1)) = k4_xboole_0(X0,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))) ) | ~spl4_4),
% 1.51/0.57    inference(superposition,[],[f54,f82])).
% 1.51/0.57  fof(f82,plain,(
% 1.51/0.57    k3_tarski(k1_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))) = k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))) | ~spl4_4),
% 1.51/0.57    inference(avatar_component_clause,[],[f80])).
% 1.51/0.57  fof(f54,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X2)))) )),
% 1.51/0.57    inference(definition_unfolding,[],[f43,f50])).
% 1.51/0.57  fof(f43,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.51/0.57    inference(cnf_transformation,[],[f5])).
% 1.51/0.57  fof(f5,axiom,(
% 1.51/0.57    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.51/0.57  fof(f187,plain,(
% 1.51/0.57    ~r1_tarski(sK1,k3_tarski(k1_enumset1(sK0,sK0,sK1))) | spl4_15),
% 1.51/0.57    inference(avatar_component_clause,[],[f185])).
% 1.51/0.57  fof(f192,plain,(
% 1.51/0.57    ~spl4_15 | spl4_16 | ~spl4_14),
% 1.51/0.57    inference(avatar_split_clause,[],[f176,f172,f189,f185])).
% 1.51/0.57  fof(f172,plain,(
% 1.51/0.57    spl4_14 <=> r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK1)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.51/0.57  fof(f176,plain,(
% 1.51/0.57    sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~r1_tarski(sK1,k3_tarski(k1_enumset1(sK0,sK0,sK1))) | ~spl4_14),
% 1.51/0.57    inference(resolution,[],[f174,f36])).
% 1.51/0.57  fof(f174,plain,(
% 1.51/0.57    r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK1) | ~spl4_14),
% 1.51/0.57    inference(avatar_component_clause,[],[f172])).
% 1.51/0.57  fof(f175,plain,(
% 1.51/0.57    spl4_14 | ~spl4_12),
% 1.51/0.57    inference(avatar_split_clause,[],[f170,f163,f172])).
% 1.51/0.57  fof(f163,plain,(
% 1.51/0.57    spl4_12 <=> r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK1))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.51/0.57  fof(f170,plain,(
% 1.51/0.57    r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),sK1) | ~spl4_12),
% 1.51/0.57    inference(resolution,[],[f165,f58])).
% 1.51/0.57  fof(f165,plain,(
% 1.51/0.57    r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK1)) | ~spl4_12),
% 1.51/0.57    inference(avatar_component_clause,[],[f163])).
% 1.51/0.57  fof(f169,plain,(
% 1.51/0.57    spl4_12 | spl4_13 | ~spl4_4),
% 1.51/0.57    inference(avatar_split_clause,[],[f118,f80,f167,f163])).
% 1.51/0.57  fof(f118,plain,(
% 1.51/0.57    ( ! [X1] : (~r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k4_xboole_0(X1,k1_zfmisc_1(sK0))) | r2_hidden(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k1_zfmisc_1(sK1))) ) | ~spl4_4),
% 1.51/0.57    inference(resolution,[],[f112,f56])).
% 1.51/0.57  fof(f112,plain,(
% 1.51/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k3_tarski(k1_enumset1(sK0,sK0,sK1))) | ~r2_hidden(X0,k4_xboole_0(X1,k1_zfmisc_1(sK0))) | r2_hidden(X0,k1_zfmisc_1(sK1))) ) | ~spl4_4),
% 1.51/0.57    inference(resolution,[],[f99,f57])).
% 1.51/0.57  fof(f99,plain,(
% 1.51/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))) | r2_hidden(X0,k1_zfmisc_1(sK1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_zfmisc_1(sK0)))) ) | ~spl4_4),
% 1.51/0.57    inference(resolution,[],[f93,f59])).
% 1.51/0.57  fof(f93,plain,(
% 1.51/0.57    ( ! [X2,X3] : (~r2_hidden(X3,k4_xboole_0(k4_xboole_0(X2,k1_zfmisc_1(sK0)),k1_zfmisc_1(sK1))) | ~r2_hidden(X3,k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))) ) | ~spl4_4),
% 1.51/0.57    inference(superposition,[],[f60,f84])).
% 1.51/0.57  fof(f83,plain,(
% 1.51/0.57    spl4_4),
% 1.51/0.57    inference(avatar_split_clause,[],[f51,f80])).
% 1.51/0.57  fof(f51,plain,(
% 1.51/0.57    k3_tarski(k1_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))) = k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))),
% 1.51/0.57    inference(definition_unfolding,[],[f28,f50,f50])).
% 1.51/0.57  fof(f28,plain,(
% 1.51/0.57    k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1))),
% 1.51/0.57    inference(cnf_transformation,[],[f16])).
% 1.51/0.57  fof(f16,plain,(
% 1.51/0.57    ~r3_xboole_0(sK0,sK1) & k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1))),
% 1.51/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f15])).
% 1.51/0.57  fof(f15,plain,(
% 1.51/0.57    ? [X0,X1] : (~r3_xboole_0(X0,X1) & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1))) => (~r3_xboole_0(sK0,sK1) & k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 1.51/0.57    introduced(choice_axiom,[])).
% 1.51/0.57  fof(f13,plain,(
% 1.51/0.57    ? [X0,X1] : (~r3_xboole_0(X0,X1) & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 1.51/0.57    inference(ennf_transformation,[],[f11])).
% 1.51/0.57  fof(f11,negated_conjecture,(
% 1.51/0.57    ~! [X0,X1] : (k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) => r3_xboole_0(X0,X1))),
% 1.51/0.57    inference(negated_conjecture,[],[f10])).
% 1.51/0.57  fof(f10,conjecture,(
% 1.51/0.57    ! [X0,X1] : (k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) => r3_xboole_0(X0,X1))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_zfmisc_1)).
% 1.51/0.57  fof(f78,plain,(
% 1.51/0.57    ~spl4_3 | spl4_1),
% 1.51/0.57    inference(avatar_split_clause,[],[f68,f63,f75])).
% 1.51/0.57  fof(f75,plain,(
% 1.51/0.57    spl4_3 <=> r1_tarski(sK1,sK0)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.51/0.57  fof(f63,plain,(
% 1.51/0.57    spl4_1 <=> r3_xboole_0(sK0,sK1)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.51/0.57  fof(f68,plain,(
% 1.51/0.57    ~r1_tarski(sK1,sK0) | spl4_1),
% 1.51/0.57    inference(resolution,[],[f65,f38])).
% 1.51/0.57  fof(f38,plain,(
% 1.51/0.57    ( ! [X0,X1] : (r3_xboole_0(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f14])).
% 1.51/0.57  fof(f14,plain,(
% 1.51/0.57    ! [X0,X1] : (r3_xboole_0(X0,X1) | (~r1_tarski(X1,X0) & ~r1_tarski(X0,X1)))),
% 1.51/0.57    inference(ennf_transformation,[],[f12])).
% 1.51/0.57  fof(f12,plain,(
% 1.51/0.57    ! [X0,X1] : ((r1_tarski(X1,X0) | r1_tarski(X0,X1)) => r3_xboole_0(X0,X1))),
% 1.51/0.57    inference(unused_predicate_definition_removal,[],[f4])).
% 1.51/0.57  fof(f4,axiom,(
% 1.51/0.57    ! [X0,X1] : (r3_xboole_0(X0,X1) <=> (r1_tarski(X1,X0) | r1_tarski(X0,X1)))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).
% 1.51/0.57  fof(f65,plain,(
% 1.51/0.57    ~r3_xboole_0(sK0,sK1) | spl4_1),
% 1.51/0.57    inference(avatar_component_clause,[],[f63])).
% 1.51/0.57  fof(f73,plain,(
% 1.51/0.57    ~spl4_2 | spl4_1),
% 1.51/0.57    inference(avatar_split_clause,[],[f67,f63,f70])).
% 1.51/0.57  fof(f67,plain,(
% 1.51/0.57    ~r1_tarski(sK0,sK1) | spl4_1),
% 1.51/0.57    inference(resolution,[],[f65,f37])).
% 1.51/0.57  fof(f37,plain,(
% 1.51/0.57    ( ! [X0,X1] : (r3_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f14])).
% 1.51/0.57  fof(f66,plain,(
% 1.51/0.57    ~spl4_1),
% 1.51/0.57    inference(avatar_split_clause,[],[f29,f63])).
% 1.51/0.57  fof(f29,plain,(
% 1.51/0.57    ~r3_xboole_0(sK0,sK1)),
% 1.51/0.57    inference(cnf_transformation,[],[f16])).
% 1.51/0.57  % SZS output end Proof for theBenchmark
% 1.51/0.57  % (22279)------------------------------
% 1.51/0.57  % (22279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (22279)Termination reason: Refutation
% 1.51/0.57  
% 1.51/0.57  % (22279)Memory used [KB]: 10874
% 1.51/0.57  % (22279)Time elapsed: 0.170 s
% 1.51/0.57  % (22279)------------------------------
% 1.51/0.57  % (22279)------------------------------
% 1.51/0.57  % (22268)Success in time 0.216 s
%------------------------------------------------------------------------------
