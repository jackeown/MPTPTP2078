%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 236 expanded)
%              Number of leaves         :   22 (  68 expanded)
%              Depth                    :   15
%              Number of atoms          :  400 ( 799 expanded)
%              Number of equality atoms :  144 ( 295 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f443,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f86,f107,f109,f124,f398,f407,f435,f442])).

fof(f442,plain,
    ( ~ spl4_2
    | spl4_5
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f441])).

fof(f441,plain,
    ( $false
    | ~ spl4_2
    | spl4_5
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f440])).

fof(f440,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl4_2
    | spl4_5
    | ~ spl4_6 ),
    inference(superposition,[],[f438,f84])).

fof(f84,plain,
    ( k1_xboole_0 = k11_relat_1(sK2,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl4_2
  <=> k1_xboole_0 = k11_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f438,plain,
    ( k1_xboole_0 != k11_relat_1(sK2,sK1)
    | spl4_5
    | ~ spl4_6 ),
    inference(resolution,[],[f122,f406])).

fof(f406,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_relat_1(sK2),k1_enumset1(X0,X0,X0))
        | k1_xboole_0 != k11_relat_1(sK2,X0) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f405])).

fof(f405,plain,
    ( spl4_6
  <=> ! [X0] :
        ( k1_xboole_0 != k11_relat_1(sK2,X0)
        | r1_xboole_0(k1_relat_1(sK2),k1_enumset1(X0,X0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f122,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK2),k1_enumset1(sK1,sK1,sK1))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl4_5
  <=> r1_xboole_0(k1_relat_1(sK2),k1_enumset1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f435,plain,
    ( ~ spl4_1
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f429])).

fof(f429,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(resolution,[],[f428,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(resolution,[],[f76,f75])).

fof(f75,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK3(X0,X1,X2,X3) != X0
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X0
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X2
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK3(X0,X1,X2,X3) != X0
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X0
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X2
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f76,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f23,f24])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f428,plain,
    ( ~ r2_hidden(sK1,k1_enumset1(sK1,sK1,sK1))
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(resolution,[],[f424,f79])).

fof(f79,plain,
    ( r2_hidden(sK1,k1_relat_1(sK2))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl4_1
  <=> r2_hidden(sK1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f424,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ r2_hidden(X0,k1_enumset1(sK1,sK1,sK1)) )
    | ~ spl4_5 ),
    inference(resolution,[],[f413,f91])).

fof(f91,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(resolution,[],[f72,f45])).

fof(f45,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k1_enumset1(X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f58,f49])).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f413,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k1_xboole_0)
        | ~ r2_hidden(X1,k1_enumset1(sK1,sK1,sK1))
        | ~ r2_hidden(X1,k1_relat_1(sK2)) )
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f411,f43])).

fof(f43,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f411,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k1_relat_1(k1_xboole_0))
        | ~ r2_hidden(X1,k1_enumset1(sK1,sK1,sK1))
        | ~ r2_hidden(X1,k1_relat_1(sK2)) )
    | ~ spl4_5 ),
    inference(superposition,[],[f395,f125])).

fof(f125,plain,
    ( k1_xboole_0 = k7_relat_1(sK2,k1_enumset1(sK1,sK1,sK1))
    | ~ spl4_5 ),
    inference(resolution,[],[f123,f110])).

fof(f110,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k1_relat_1(sK2),X0)
      | k1_xboole_0 = k7_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f53,f40])).

fof(f40,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK2,sK1)
      | ~ r2_hidden(sK1,k1_relat_1(sK2)) )
    & ( k1_xboole_0 != k11_relat_1(sK2,sK1)
      | r2_hidden(sK1,k1_relat_1(sK2)) )
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK2,sK1)
        | ~ r2_hidden(sK1,k1_relat_1(sK2)) )
      & ( k1_xboole_0 != k11_relat_1(sK2,sK1)
        | r2_hidden(sK1,k1_relat_1(sK2)) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f123,plain,
    ( r1_xboole_0(k1_relat_1(sK2),k1_enumset1(sK1,sK1,sK1))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f121])).

fof(f395,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1)))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f57,f40])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f407,plain,
    ( ~ spl4_3
    | spl4_6 ),
    inference(avatar_split_clause,[],[f403,f405,f101])).

fof(f101,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f403,plain,(
    ! [X0] :
      ( k1_xboole_0 != k11_relat_1(sK2,X0)
      | r1_xboole_0(k1_relat_1(sK2),k1_enumset1(X0,X0,X0))
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f50,f392])).

fof(f392,plain,(
    ! [X0] : k9_relat_1(sK2,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK2,X0) ),
    inference(resolution,[],[f70,f40])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f47,f69])).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f49])).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(f398,plain,
    ( spl4_1
    | spl4_2
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f397])).

fof(f397,plain,
    ( $false
    | spl4_1
    | spl4_2
    | ~ spl4_4 ),
    inference(trivial_inequality_removal,[],[f396])).

fof(f396,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl4_1
    | spl4_2
    | ~ spl4_4 ),
    inference(superposition,[],[f83,f394])).

fof(f394,plain,
    ( k1_xboole_0 = k11_relat_1(sK2,sK1)
    | spl4_1
    | ~ spl4_4 ),
    inference(resolution,[],[f393,f80])).

fof(f80,plain,
    ( ~ r2_hidden(sK1,k1_relat_1(sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f393,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_relat_1(sK2))
        | k1_xboole_0 = k11_relat_1(sK2,X0) )
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f115,f392])).

fof(f115,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_relat_1(sK2))
        | k1_xboole_0 = k9_relat_1(sK2,k1_enumset1(X0,X0,X0)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f106,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_enumset1(X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f69])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f106,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k1_relat_1(sK2))
        | k1_xboole_0 = k9_relat_1(sK2,X0) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl4_4
  <=> ! [X0] :
        ( k1_xboole_0 = k9_relat_1(sK2,X0)
        | ~ r1_xboole_0(X0,k1_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f83,plain,
    ( k1_xboole_0 != k11_relat_1(sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f124,plain,
    ( ~ spl4_3
    | spl4_5
    | spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f119,f105,f78,f121,f101])).

fof(f119,plain,
    ( r1_xboole_0(k1_relat_1(sK2),k1_enumset1(sK1,sK1,sK1))
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_4 ),
    inference(trivial_inequality_removal,[],[f118])).

fof(f118,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK2),k1_enumset1(sK1,sK1,sK1))
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_4 ),
    inference(superposition,[],[f50,f117])).

fof(f117,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k1_enumset1(sK1,sK1,sK1))
    | spl4_1
    | ~ spl4_4 ),
    inference(resolution,[],[f115,f80])).

fof(f109,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | spl4_3 ),
    inference(resolution,[],[f103,f40])).

fof(f103,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f107,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f99,f105,f101])).

fof(f99,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(sK2,X0)
      | ~ r1_xboole_0(X0,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(trivial_inequality_removal,[],[f98])).

fof(f98,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = k9_relat_1(sK2,X0)
      | ~ r1_xboole_0(X0,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f97,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

fof(f97,plain,(
    ! [X0] :
      ( k1_xboole_0 != k7_relat_1(sK2,X0)
      | k1_xboole_0 = k9_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f96,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k1_relat_1(sK2),X0)
      | k1_xboole_0 = k9_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f51,f40])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f96,plain,(
    ! [X0] :
      ( r1_xboole_0(k1_relat_1(sK2),X0)
      | k1_xboole_0 != k7_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f52,f40])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 != k7_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f86,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f41,f82,f78])).

fof(f41,plain,
    ( k1_xboole_0 != k11_relat_1(sK2,sK1)
    | r2_hidden(sK1,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f85,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f42,f82,f78])).

fof(f42,plain,
    ( k1_xboole_0 = k11_relat_1(sK2,sK1)
    | ~ r2_hidden(sK1,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (27503)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (27513)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.49  % (27495)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (27514)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (27506)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (27491)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (27504)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (27492)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (27498)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (27503)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f443,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f85,f86,f107,f109,f124,f398,f407,f435,f442])).
% 0.20/0.51  fof(f442,plain,(
% 0.20/0.51    ~spl4_2 | spl4_5 | ~spl4_6),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f441])).
% 0.20/0.51  fof(f441,plain,(
% 0.20/0.51    $false | (~spl4_2 | spl4_5 | ~spl4_6)),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f440])).
% 0.20/0.51  fof(f440,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0 | (~spl4_2 | spl4_5 | ~spl4_6)),
% 0.20/0.51    inference(superposition,[],[f438,f84])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    k1_xboole_0 = k11_relat_1(sK2,sK1) | ~spl4_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f82])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    spl4_2 <=> k1_xboole_0 = k11_relat_1(sK2,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.51  fof(f438,plain,(
% 0.20/0.51    k1_xboole_0 != k11_relat_1(sK2,sK1) | (spl4_5 | ~spl4_6)),
% 0.20/0.51    inference(resolution,[],[f122,f406])).
% 0.20/0.51  fof(f406,plain,(
% 0.20/0.51    ( ! [X0] : (r1_xboole_0(k1_relat_1(sK2),k1_enumset1(X0,X0,X0)) | k1_xboole_0 != k11_relat_1(sK2,X0)) ) | ~spl4_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f405])).
% 0.20/0.51  fof(f405,plain,(
% 0.20/0.51    spl4_6 <=> ! [X0] : (k1_xboole_0 != k11_relat_1(sK2,X0) | r1_xboole_0(k1_relat_1(sK2),k1_enumset1(X0,X0,X0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    ~r1_xboole_0(k1_relat_1(sK2),k1_enumset1(sK1,sK1,sK1)) | spl4_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f121])).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    spl4_5 <=> r1_xboole_0(k1_relat_1(sK2),k1_enumset1(sK1,sK1,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.51  fof(f435,plain,(
% 0.20/0.51    ~spl4_1 | ~spl4_5),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f429])).
% 0.20/0.51  fof(f429,plain,(
% 0.20/0.51    $false | (~spl4_1 | ~spl4_5)),
% 0.20/0.51    inference(resolution,[],[f428,f87])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X1,X2))) )),
% 0.20/0.51    inference(resolution,[],[f76,f75])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    ( ! [X0,X5,X3,X1] : (~sP0(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 0.20/0.51    inference(equality_resolution,[],[f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK3(X0,X1,X2,X3) != X0 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X2) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X0 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X2 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X0 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X2) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X0 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X2 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.20/0.51    inference(rectify,[],[f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.20/0.51    inference(flattening,[],[f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.20/0.51    inference(nnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.20/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 0.20/0.51    inference(equality_resolution,[],[f67])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.51    inference(cnf_transformation,[],[f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.51    inference(nnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 0.20/0.51    inference(definition_folding,[],[f23,f24])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.20/0.51  fof(f428,plain,(
% 0.20/0.51    ~r2_hidden(sK1,k1_enumset1(sK1,sK1,sK1)) | (~spl4_1 | ~spl4_5)),
% 0.20/0.51    inference(resolution,[],[f424,f79])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    r2_hidden(sK1,k1_relat_1(sK2)) | ~spl4_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f78])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    spl4_1 <=> r2_hidden(sK1,k1_relat_1(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.51  fof(f424,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | ~r2_hidden(X0,k1_enumset1(sK1,sK1,sK1))) ) | ~spl4_5),
% 0.20/0.51    inference(resolution,[],[f413,f91])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 0.20/0.51    inference(resolution,[],[f72,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_xboole_0(k1_enumset1(X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f58,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.20/0.51  fof(f413,plain,(
% 0.20/0.51    ( ! [X1] : (r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,k1_enumset1(sK1,sK1,sK1)) | ~r2_hidden(X1,k1_relat_1(sK2))) ) | ~spl4_5),
% 0.20/0.51    inference(forward_demodulation,[],[f411,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.51  fof(f411,plain,(
% 0.20/0.51    ( ! [X1] : (r2_hidden(X1,k1_relat_1(k1_xboole_0)) | ~r2_hidden(X1,k1_enumset1(sK1,sK1,sK1)) | ~r2_hidden(X1,k1_relat_1(sK2))) ) | ~spl4_5),
% 0.20/0.51    inference(superposition,[],[f395,f125])).
% 0.20/0.51  fof(f125,plain,(
% 0.20/0.51    k1_xboole_0 = k7_relat_1(sK2,k1_enumset1(sK1,sK1,sK1)) | ~spl4_5),
% 0.20/0.51    inference(resolution,[],[f123,f110])).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_xboole_0(k1_relat_1(sK2),X0) | k1_xboole_0 = k7_relat_1(sK2,X0)) )),
% 0.20/0.51    inference(resolution,[],[f53,f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    v1_relat_1(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    (k1_xboole_0 = k11_relat_1(sK2,sK1) | ~r2_hidden(sK1,k1_relat_1(sK2))) & (k1_xboole_0 != k11_relat_1(sK2,sK1) | r2_hidden(sK1,k1_relat_1(sK2))) & v1_relat_1(sK2)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK2,sK1) | ~r2_hidden(sK1,k1_relat_1(sK2))) & (k1_xboole_0 != k11_relat_1(sK2,sK1) | r2_hidden(sK1,k1_relat_1(sK2))) & v1_relat_1(sK2))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.20/0.51    inference(flattening,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.20/0.51    inference(negated_conjecture,[],[f13])).
% 0.20/0.51  fof(f13,conjecture,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    r1_xboole_0(k1_relat_1(sK2),k1_enumset1(sK1,sK1,sK1)) | ~spl4_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f121])).
% 0.20/0.51  fof(f395,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1))) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(sK2))) )),
% 0.20/0.51    inference(resolution,[],[f57,f40])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(nnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).
% 0.20/0.51  fof(f407,plain,(
% 0.20/0.51    ~spl4_3 | spl4_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f403,f405,f101])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    spl4_3 <=> v1_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.51  fof(f403,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 != k11_relat_1(sK2,X0) | r1_xboole_0(k1_relat_1(sK2),k1_enumset1(X0,X0,X0)) | ~v1_relat_1(sK2)) )),
% 0.20/0.51    inference(superposition,[],[f50,f392])).
% 0.20/0.51  fof(f392,plain,(
% 0.20/0.51    ( ! [X0] : (k9_relat_1(sK2,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK2,X0)) )),
% 0.20/0.51    inference(resolution,[],[f70,f40])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f47,f69])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f46,f49])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
% 0.20/0.51  fof(f398,plain,(
% 0.20/0.51    spl4_1 | spl4_2 | ~spl4_4),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f397])).
% 0.20/0.51  fof(f397,plain,(
% 0.20/0.51    $false | (spl4_1 | spl4_2 | ~spl4_4)),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f396])).
% 0.20/0.51  fof(f396,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0 | (spl4_1 | spl4_2 | ~spl4_4)),
% 0.20/0.51    inference(superposition,[],[f83,f394])).
% 0.20/0.51  fof(f394,plain,(
% 0.20/0.51    k1_xboole_0 = k11_relat_1(sK2,sK1) | (spl4_1 | ~spl4_4)),
% 0.20/0.51    inference(resolution,[],[f393,f80])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    ~r2_hidden(sK1,k1_relat_1(sK2)) | spl4_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f78])).
% 0.20/0.51  fof(f393,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK2)) | k1_xboole_0 = k11_relat_1(sK2,X0)) ) | ~spl4_4),
% 0.20/0.51    inference(backward_demodulation,[],[f115,f392])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK2)) | k1_xboole_0 = k9_relat_1(sK2,k1_enumset1(X0,X0,X0))) ) | ~spl4_4),
% 0.20/0.51    inference(resolution,[],[f106,f71])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_xboole_0(k1_enumset1(X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f54,f69])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_xboole_0(X0,k1_relat_1(sK2)) | k1_xboole_0 = k9_relat_1(sK2,X0)) ) | ~spl4_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f105])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    spl4_4 <=> ! [X0] : (k1_xboole_0 = k9_relat_1(sK2,X0) | ~r1_xboole_0(X0,k1_relat_1(sK2)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    k1_xboole_0 != k11_relat_1(sK2,sK1) | spl4_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f82])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    ~spl4_3 | spl4_5 | spl4_1 | ~spl4_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f119,f105,f78,f121,f101])).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    r1_xboole_0(k1_relat_1(sK2),k1_enumset1(sK1,sK1,sK1)) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_4)),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f118])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK2),k1_enumset1(sK1,sK1,sK1)) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_4)),
% 0.20/0.51    inference(superposition,[],[f50,f117])).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    k1_xboole_0 = k9_relat_1(sK2,k1_enumset1(sK1,sK1,sK1)) | (spl4_1 | ~spl4_4)),
% 0.20/0.51    inference(resolution,[],[f115,f80])).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    spl4_3),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f108])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    $false | spl4_3),
% 0.20/0.51    inference(resolution,[],[f103,f40])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    ~v1_relat_1(sK2) | spl4_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f101])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    ~spl4_3 | spl4_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f99,f105,f101])).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK2,X0) | ~r1_xboole_0(X0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f98])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k9_relat_1(sK2,X0) | ~r1_xboole_0(X0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 0.20/0.51    inference(superposition,[],[f97,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 != k7_relat_1(sK2,X0) | k1_xboole_0 = k9_relat_1(sK2,X0)) )),
% 0.20/0.51    inference(resolution,[],[f96,f92])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_xboole_0(k1_relat_1(sK2),X0) | k1_xboole_0 = k9_relat_1(sK2,X0)) )),
% 0.20/0.51    inference(resolution,[],[f51,f40])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f30])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    ( ! [X0] : (r1_xboole_0(k1_relat_1(sK2),X0) | k1_xboole_0 != k7_relat_1(sK2,X0)) )),
% 0.20/0.51    inference(resolution,[],[f52,f40])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 != k7_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    spl4_1 | ~spl4_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f41,f82,f78])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    k1_xboole_0 != k11_relat_1(sK2,sK1) | r2_hidden(sK1,k1_relat_1(sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ~spl4_1 | spl4_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f42,f82,f78])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    k1_xboole_0 = k11_relat_1(sK2,sK1) | ~r2_hidden(sK1,k1_relat_1(sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (27503)------------------------------
% 0.20/0.51  % (27503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (27503)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (27503)Memory used [KB]: 6396
% 0.20/0.51  % (27503)Time elapsed: 0.104 s
% 0.20/0.51  % (27503)------------------------------
% 0.20/0.51  % (27503)------------------------------
% 0.20/0.51  % (27490)Success in time 0.158 s
%------------------------------------------------------------------------------
