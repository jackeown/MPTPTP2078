%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 342 expanded)
%              Number of leaves         :   16 ( 101 expanded)
%              Depth                    :   13
%              Number of atoms          :  280 (1462 expanded)
%              Number of equality atoms :   31 ( 205 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f269,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f134,f174,f192,f233,f265,f268])).

fof(f268,plain,(
    spl9_10 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | spl9_10 ),
    inference(subsumption_resolution,[],[f266,f57])).

fof(f57,plain,(
    r2_hidden(sK1,k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f54,f47])).

fof(f47,plain,(
    r2_hidden(sK1,k4_xboole_0(k2_zfmisc_1(sK2,sK3),k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)))) ),
    inference(definition_unfolding,[],[f26,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f26,plain,(
    r2_hidden(sK1,k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ! [X5,X6] :
        ( ~ r2_hidden(X6,k3_xboole_0(sK3,sK5))
        | ~ r2_hidden(X5,k3_xboole_0(sK2,sK4))
        | k4_tarski(X5,X6) != sK1 )
    & r2_hidden(sK1,k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f8,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ! [X5,X6] :
            ( ~ r2_hidden(X6,k3_xboole_0(X2,X4))
            | ~ r2_hidden(X5,k3_xboole_0(X1,X3))
            | k4_tarski(X5,X6) != X0 )
        & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) )
   => ( ! [X6,X5] :
          ( ~ r2_hidden(X6,k3_xboole_0(sK3,sK5))
          | ~ r2_hidden(X5,k3_xboole_0(sK2,sK4))
          | k4_tarski(X5,X6) != sK1 )
      & r2_hidden(sK1,k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ! [X5,X6] :
          ( ~ r2_hidden(X6,k3_xboole_0(X2,X4))
          | ~ r2_hidden(X5,k3_xboole_0(X1,X3))
          | k4_tarski(X5,X6) != X0 )
      & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ~ ( ! [X5,X6] :
              ~ ( r2_hidden(X6,k3_xboole_0(X2,X4))
                & r2_hidden(X5,k3_xboole_0(X1,X3))
                & k4_tarski(X5,X6) = X0 )
          & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( ! [X5,X6] :
            ~ ( r2_hidden(X6,k3_xboole_0(X2,X4))
              & r2_hidden(X5,k3_xboole_0(X1,X3))
              & k4_tarski(X5,X6) = X0 )
        & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_zfmisc_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f32,f52])).

fof(f52,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f38,f28])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f10])).

fof(f10,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK6(X0,X1,X2),X0)
              & r2_hidden(sK6(X0,X1,X2),X1) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f18,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X0)
            & r2_hidden(sK6(X0,X1,X2),X1) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f266,plain,
    ( ~ r2_hidden(sK1,k2_zfmisc_1(sK2,sK3))
    | spl9_10 ),
    inference(resolution,[],[f232,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X1,X2,X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(resolution,[],[f43,f50])).

fof(f50,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(X3,X0)
      | r2_hidden(sK7(X1,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k4_tarski(sK7(X1,X2,X3),sK8(X1,X2,X3)) = X3
        & r2_hidden(sK8(X1,X2,X3),X2)
        & r2_hidden(sK7(X1,X2,X3),X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f9,f24])).

fof(f24,plain,(
    ! [X3,X2,X1] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
     => ( k4_tarski(sK7(X1,X2,X3),sK8(X1,X2,X3)) = X3
        & r2_hidden(sK8(X1,X2,X3),X2)
        & r2_hidden(sK7(X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(f232,plain,
    ( ~ r2_hidden(sK7(sK2,sK3,sK1),sK2)
    | spl9_10 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl9_10
  <=> r2_hidden(sK7(sK2,sK3,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f265,plain,(
    spl9_9 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | spl9_9 ),
    inference(subsumption_resolution,[],[f263,f228])).

fof(f228,plain,
    ( ~ r2_hidden(sK7(sK2,sK3,sK1),sK4)
    | spl9_9 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl9_9
  <=> r2_hidden(sK7(sK2,sK3,sK1),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f263,plain,(
    r2_hidden(sK7(sK2,sK3,sK1),sK4) ),
    inference(resolution,[],[f101,f58])).

fof(f58,plain,(
    r2_hidden(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[],[f55,f47])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f33,f52])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f101,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK1,k2_zfmisc_1(X4,X5))
      | r2_hidden(sK7(sK2,sK3,sK1),X4) ) ),
    inference(superposition,[],[f40,f88])).

fof(f88,plain,(
    sK1 = k4_tarski(sK7(sK2,sK3,sK1),sK8(sK2,sK3,sK1)) ),
    inference(resolution,[],[f84,f57])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(sK7(X1,X2,X0),sK8(X1,X2,X0)) = X0 ) ),
    inference(resolution,[],[f45,f50])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(X3,X0)
      | k4_tarski(sK7(X1,X2,X3),sK8(X1,X2,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f233,plain,
    ( ~ spl9_9
    | ~ spl9_10
    | spl9_2 ),
    inference(avatar_split_clause,[],[f224,f108,f230,f226])).

fof(f108,plain,
    ( spl9_2
  <=> r2_hidden(sK7(sK2,sK3,sK1),k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f224,plain,
    ( ~ r2_hidden(sK7(sK2,sK3,sK1),sK2)
    | ~ r2_hidden(sK7(sK2,sK3,sK1),sK4)
    | spl9_2 ),
    inference(resolution,[],[f110,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1)))
      | ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f34,f52])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f110,plain,
    ( ~ r2_hidden(sK7(sK2,sK3,sK1),k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)))
    | spl9_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f192,plain,(
    spl9_4 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | spl9_4 ),
    inference(subsumption_resolution,[],[f190,f57])).

fof(f190,plain,
    ( ~ r2_hidden(sK1,k2_zfmisc_1(sK2,sK3))
    | spl9_4 ),
    inference(resolution,[],[f133,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X1,X2,X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(resolution,[],[f44,f50])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(X3,X0)
      | r2_hidden(sK8(X1,X2,X3),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f133,plain,
    ( ~ r2_hidden(sK8(sK2,sK3,sK1),sK3)
    | spl9_4 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl9_4
  <=> r2_hidden(sK8(sK2,sK3,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f174,plain,(
    spl9_3 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | spl9_3 ),
    inference(subsumption_resolution,[],[f172,f129])).

fof(f129,plain,
    ( ~ r2_hidden(sK8(sK2,sK3,sK1),sK5)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl9_3
  <=> r2_hidden(sK8(sK2,sK3,sK1),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f172,plain,(
    r2_hidden(sK8(sK2,sK3,sK1),sK5) ),
    inference(resolution,[],[f100,f58])).

fof(f100,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK1,k2_zfmisc_1(X2,X3))
      | r2_hidden(sK8(sK2,sK3,sK1),X3) ) ),
    inference(superposition,[],[f41,f88])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f134,plain,
    ( ~ spl9_3
    | ~ spl9_4
    | spl9_1 ),
    inference(avatar_split_clause,[],[f125,f104,f131,f127])).

fof(f104,plain,
    ( spl9_1
  <=> r2_hidden(sK8(sK2,sK3,sK1),k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f125,plain,
    ( ~ r2_hidden(sK8(sK2,sK3,sK1),sK3)
    | ~ r2_hidden(sK8(sK2,sK3,sK1),sK5)
    | spl9_1 ),
    inference(resolution,[],[f106,f59])).

fof(f106,plain,
    ( ~ r2_hidden(sK8(sK2,sK3,sK1),k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f111,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f102,f108,f104])).

fof(f102,plain,
    ( ~ r2_hidden(sK7(sK2,sK3,sK1),k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)))
    | ~ r2_hidden(sK8(sK2,sK3,sK1),k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) ),
    inference(trivial_inequality_removal,[],[f98])).

fof(f98,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK7(sK2,sK3,sK1),k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)))
    | ~ r2_hidden(sK8(sK2,sK3,sK1),k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) ),
    inference(superposition,[],[f46,f88])).

fof(f46,plain,(
    ! [X6,X5] :
      ( k4_tarski(X5,X6) != sK1
      | ~ r2_hidden(X5,k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)))
      | ~ r2_hidden(X6,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) ) ),
    inference(definition_unfolding,[],[f27,f28,f28])).

fof(f27,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X6,k3_xboole_0(sK3,sK5))
      | ~ r2_hidden(X5,k3_xboole_0(sK2,sK4))
      | k4_tarski(X5,X6) != sK1 ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:26:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.47  % (27952)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.48  % (27975)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.48  % (27975)Refutation not found, incomplete strategy% (27975)------------------------------
% 0.22/0.48  % (27975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (27975)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (27975)Memory used [KB]: 10618
% 0.22/0.48  % (27975)Time elapsed: 0.061 s
% 0.22/0.48  % (27975)------------------------------
% 0.22/0.48  % (27975)------------------------------
% 0.22/0.50  % (27962)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.51  % (27951)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (27953)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.51  % (27954)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (27965)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.51  % (27965)Refutation not found, incomplete strategy% (27965)------------------------------
% 0.22/0.51  % (27965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (27965)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (27965)Memory used [KB]: 1663
% 0.22/0.51  % (27965)Time elapsed: 0.069 s
% 0.22/0.51  % (27965)------------------------------
% 0.22/0.51  % (27965)------------------------------
% 0.22/0.51  % (27978)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.51  % (27978)Refutation not found, incomplete strategy% (27978)------------------------------
% 0.22/0.51  % (27978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (27963)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (27966)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (27968)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.52  % (27970)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.52  % (27973)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (27974)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  % (27978)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (27978)Memory used [KB]: 6140
% 0.22/0.53  % (27978)Time elapsed: 0.105 s
% 0.22/0.53  % (27978)------------------------------
% 0.22/0.53  % (27978)------------------------------
% 0.22/0.53  % (27957)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (27958)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (27955)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (27967)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (27959)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (27967)Refutation not found, incomplete strategy% (27967)------------------------------
% 0.22/0.54  % (27967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (27967)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (27967)Memory used [KB]: 10746
% 0.22/0.54  % (27967)Time elapsed: 0.130 s
% 0.22/0.54  % (27967)------------------------------
% 0.22/0.54  % (27967)------------------------------
% 0.22/0.55  % (27976)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (27977)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (27979)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (27956)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (27960)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (27964)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.55  % (27961)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (27971)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  % (27957)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f269,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f111,f134,f174,f192,f233,f265,f268])).
% 0.22/0.56  fof(f268,plain,(
% 0.22/0.56    spl9_10),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f267])).
% 0.22/0.56  fof(f267,plain,(
% 0.22/0.56    $false | spl9_10),
% 0.22/0.56    inference(subsumption_resolution,[],[f266,f57])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    r2_hidden(sK1,k2_zfmisc_1(sK2,sK3))),
% 0.22/0.56    inference(resolution,[],[f54,f47])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    r2_hidden(sK1,k4_xboole_0(k2_zfmisc_1(sK2,sK3),k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))))),
% 0.22/0.56    inference(definition_unfolding,[],[f26,f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    r2_hidden(sK1,k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)))),
% 0.22/0.56    inference(cnf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,plain,(
% 0.22/0.56    ! [X5,X6] : (~r2_hidden(X6,k3_xboole_0(sK3,sK5)) | ~r2_hidden(X5,k3_xboole_0(sK2,sK4)) | k4_tarski(X5,X6) != sK1) & r2_hidden(sK1,k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f8,f12])).
% 0.22/0.56  fof(f12,plain,(
% 0.22/0.56    ? [X0,X1,X2,X3,X4] : (! [X5,X6] : (~r2_hidden(X6,k3_xboole_0(X2,X4)) | ~r2_hidden(X5,k3_xboole_0(X1,X3)) | k4_tarski(X5,X6) != X0) & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))) => (! [X6,X5] : (~r2_hidden(X6,k3_xboole_0(sK3,sK5)) | ~r2_hidden(X5,k3_xboole_0(sK2,sK4)) | k4_tarski(X5,X6) != sK1) & r2_hidden(sK1,k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f8,plain,(
% 0.22/0.56    ? [X0,X1,X2,X3,X4] : (! [X5,X6] : (~r2_hidden(X6,k3_xboole_0(X2,X4)) | ~r2_hidden(X5,k3_xboole_0(X1,X3)) | k4_tarski(X5,X6) != X0) & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1,X2,X3,X4] : ~(! [X5,X6] : ~(r2_hidden(X6,k3_xboole_0(X2,X4)) & r2_hidden(X5,k3_xboole_0(X1,X3)) & k4_tarski(X5,X6) = X0) & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))))),
% 0.22/0.56    inference(negated_conjecture,[],[f6])).
% 0.22/0.56  fof(f6,conjecture,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4] : ~(! [X5,X6] : ~(r2_hidden(X6,k3_xboole_0(X2,X4)) & r2_hidden(X5,k3_xboole_0(X1,X3)) & k4_tarski(X5,X6) = X0) & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_zfmisc_1)).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | r2_hidden(X0,X1)) )),
% 0.22/0.56    inference(resolution,[],[f32,f52])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.56    inference(equality_resolution,[],[f49])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 0.22/0.56    inference(definition_unfolding,[],[f38,f28])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.22/0.56    inference(cnf_transformation,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.56    inference(nnf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.22/0.56    inference(definition_folding,[],[f1,f10])).
% 0.22/0.56  fof(f10,plain,(
% 0.22/0.56    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f18,f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.56    inference(rectify,[],[f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.56    inference(flattening,[],[f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.56    inference(nnf_transformation,[],[f10])).
% 0.22/0.56  fof(f266,plain,(
% 0.22/0.56    ~r2_hidden(sK1,k2_zfmisc_1(sK2,sK3)) | spl9_10),
% 0.22/0.56    inference(resolution,[],[f232,f64])).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK7(X1,X2,X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.22/0.56    inference(resolution,[],[f43,f50])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.56    inference(equality_resolution,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.56    inference(flattening,[],[f14])).
% 0.22/0.56  fof(f14,plain,(
% 0.22/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.56    inference(nnf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~r2_hidden(X3,X0) | r2_hidden(sK7(X1,X2,X3),X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((k4_tarski(sK7(X1,X2,X3),sK8(X1,X2,X3)) = X3 & r2_hidden(sK8(X1,X2,X3),X2) & r2_hidden(sK7(X1,X2,X3),X1)) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f9,f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X3,X2,X1] : (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) => (k4_tarski(sK7(X1,X2,X3),sK8(X1,X2,X3)) = X3 & r2_hidden(sK8(X1,X2,X3),X2) & r2_hidden(sK7(X1,X2,X3),X1)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f9,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).
% 0.22/0.56  fof(f232,plain,(
% 0.22/0.56    ~r2_hidden(sK7(sK2,sK3,sK1),sK2) | spl9_10),
% 0.22/0.56    inference(avatar_component_clause,[],[f230])).
% 0.22/0.56  fof(f230,plain,(
% 0.22/0.56    spl9_10 <=> r2_hidden(sK7(sK2,sK3,sK1),sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.22/0.56  fof(f265,plain,(
% 0.22/0.56    spl9_9),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f264])).
% 0.22/0.56  fof(f264,plain,(
% 0.22/0.56    $false | spl9_9),
% 0.22/0.56    inference(subsumption_resolution,[],[f263,f228])).
% 0.22/0.56  fof(f228,plain,(
% 0.22/0.56    ~r2_hidden(sK7(sK2,sK3,sK1),sK4) | spl9_9),
% 0.22/0.56    inference(avatar_component_clause,[],[f226])).
% 0.22/0.56  fof(f226,plain,(
% 0.22/0.56    spl9_9 <=> r2_hidden(sK7(sK2,sK3,sK1),sK4)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.22/0.56  fof(f263,plain,(
% 0.22/0.56    r2_hidden(sK7(sK2,sK3,sK1),sK4)),
% 0.22/0.56    inference(resolution,[],[f101,f58])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    r2_hidden(sK1,k2_zfmisc_1(sK4,sK5))),
% 0.22/0.56    inference(resolution,[],[f55,f47])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | r2_hidden(X0,X2)) )),
% 0.22/0.56    inference(resolution,[],[f33,f52])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f101,plain,(
% 0.22/0.56    ( ! [X4,X5] : (~r2_hidden(sK1,k2_zfmisc_1(X4,X5)) | r2_hidden(sK7(sK2,sK3,sK1),X4)) )),
% 0.22/0.56    inference(superposition,[],[f40,f88])).
% 0.22/0.56  fof(f88,plain,(
% 0.22/0.56    sK1 = k4_tarski(sK7(sK2,sK3,sK1),sK8(sK2,sK3,sK1))),
% 0.22/0.56    inference(resolution,[],[f84,f57])).
% 0.22/0.56  fof(f84,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK7(X1,X2,X0),sK8(X1,X2,X0)) = X0) )),
% 0.22/0.56    inference(resolution,[],[f45,f50])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~r2_hidden(X3,X0) | k4_tarski(sK7(X1,X2,X3),sK8(X1,X2,X3)) = X3) )),
% 0.22/0.56    inference(cnf_transformation,[],[f25])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.56    inference(flattening,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.56    inference(nnf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.56  fof(f233,plain,(
% 0.22/0.56    ~spl9_9 | ~spl9_10 | spl9_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f224,f108,f230,f226])).
% 0.22/0.56  fof(f108,plain,(
% 0.22/0.56    spl9_2 <=> r2_hidden(sK7(sK2,sK3,sK1),k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.22/0.56  fof(f224,plain,(
% 0.22/0.56    ~r2_hidden(sK7(sK2,sK3,sK1),sK2) | ~r2_hidden(sK7(sK2,sK3,sK1),sK4) | spl9_2),
% 0.22/0.56    inference(resolution,[],[f110,f59])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) | ~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.56    inference(resolution,[],[f34,f52])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1) | r2_hidden(X4,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f110,plain,(
% 0.22/0.56    ~r2_hidden(sK7(sK2,sK3,sK1),k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))) | spl9_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f108])).
% 0.22/0.56  fof(f192,plain,(
% 0.22/0.56    spl9_4),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f191])).
% 0.22/0.56  fof(f191,plain,(
% 0.22/0.56    $false | spl9_4),
% 0.22/0.56    inference(subsumption_resolution,[],[f190,f57])).
% 0.22/0.56  fof(f190,plain,(
% 0.22/0.56    ~r2_hidden(sK1,k2_zfmisc_1(sK2,sK3)) | spl9_4),
% 0.22/0.56    inference(resolution,[],[f133,f67])).
% 0.22/0.56  fof(f67,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK8(X1,X2,X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.22/0.56    inference(resolution,[],[f44,f50])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~r2_hidden(X3,X0) | r2_hidden(sK8(X1,X2,X3),X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f25])).
% 0.22/0.56  fof(f133,plain,(
% 0.22/0.56    ~r2_hidden(sK8(sK2,sK3,sK1),sK3) | spl9_4),
% 0.22/0.56    inference(avatar_component_clause,[],[f131])).
% 0.22/0.56  fof(f131,plain,(
% 0.22/0.56    spl9_4 <=> r2_hidden(sK8(sK2,sK3,sK1),sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.22/0.56  fof(f174,plain,(
% 0.22/0.56    spl9_3),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f173])).
% 0.22/0.56  fof(f173,plain,(
% 0.22/0.56    $false | spl9_3),
% 0.22/0.56    inference(subsumption_resolution,[],[f172,f129])).
% 0.22/0.56  fof(f129,plain,(
% 0.22/0.56    ~r2_hidden(sK8(sK2,sK3,sK1),sK5) | spl9_3),
% 0.22/0.56    inference(avatar_component_clause,[],[f127])).
% 0.22/0.56  fof(f127,plain,(
% 0.22/0.56    spl9_3 <=> r2_hidden(sK8(sK2,sK3,sK1),sK5)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.22/0.56  fof(f172,plain,(
% 0.22/0.56    r2_hidden(sK8(sK2,sK3,sK1),sK5)),
% 0.22/0.56    inference(resolution,[],[f100,f58])).
% 0.22/0.56  fof(f100,plain,(
% 0.22/0.56    ( ! [X2,X3] : (~r2_hidden(sK1,k2_zfmisc_1(X2,X3)) | r2_hidden(sK8(sK2,sK3,sK1),X3)) )),
% 0.22/0.56    inference(superposition,[],[f41,f88])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  fof(f134,plain,(
% 0.22/0.56    ~spl9_3 | ~spl9_4 | spl9_1),
% 0.22/0.56    inference(avatar_split_clause,[],[f125,f104,f131,f127])).
% 0.22/0.56  fof(f104,plain,(
% 0.22/0.56    spl9_1 <=> r2_hidden(sK8(sK2,sK3,sK1),k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.56  fof(f125,plain,(
% 0.22/0.56    ~r2_hidden(sK8(sK2,sK3,sK1),sK3) | ~r2_hidden(sK8(sK2,sK3,sK1),sK5) | spl9_1),
% 0.22/0.56    inference(resolution,[],[f106,f59])).
% 0.22/0.56  fof(f106,plain,(
% 0.22/0.56    ~r2_hidden(sK8(sK2,sK3,sK1),k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) | spl9_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f104])).
% 0.22/0.56  fof(f111,plain,(
% 0.22/0.56    ~spl9_1 | ~spl9_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f102,f108,f104])).
% 0.22/0.56  fof(f102,plain,(
% 0.22/0.56    ~r2_hidden(sK7(sK2,sK3,sK1),k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))) | ~r2_hidden(sK8(sK2,sK3,sK1),k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f98])).
% 0.22/0.56  fof(f98,plain,(
% 0.22/0.56    sK1 != sK1 | ~r2_hidden(sK7(sK2,sK3,sK1),k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))) | ~r2_hidden(sK8(sK2,sK3,sK1),k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))),
% 0.22/0.56    inference(superposition,[],[f46,f88])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ( ! [X6,X5] : (k4_tarski(X5,X6) != sK1 | ~r2_hidden(X5,k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))) | ~r2_hidden(X6,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) )),
% 0.22/0.56    inference(definition_unfolding,[],[f27,f28,f28])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ( ! [X6,X5] : (~r2_hidden(X6,k3_xboole_0(sK3,sK5)) | ~r2_hidden(X5,k3_xboole_0(sK2,sK4)) | k4_tarski(X5,X6) != sK1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f13])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (27957)------------------------------
% 0.22/0.56  % (27957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (27957)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (27957)Memory used [KB]: 11001
% 0.22/0.56  % (27957)Time elapsed: 0.125 s
% 0.22/0.56  % (27957)------------------------------
% 0.22/0.56  % (27957)------------------------------
% 0.22/0.56  % (27950)Success in time 0.198 s
%------------------------------------------------------------------------------
