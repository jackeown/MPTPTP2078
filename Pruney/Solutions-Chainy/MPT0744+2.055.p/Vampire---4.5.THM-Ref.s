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
% DateTime   : Thu Dec  3 12:55:37 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 495 expanded)
%              Number of leaves         :   27 ( 152 expanded)
%              Depth                    :   17
%              Number of atoms          :  537 (1695 expanded)
%              Number of equality atoms :  104 ( 335 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f407,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f145,f146,f194,f239,f248,f278,f310,f345,f406])).

% (27580)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f406,plain,
    ( spl9_1
    | ~ spl9_4 ),
    inference(avatar_contradiction_clause,[],[f405])).

fof(f405,plain,
    ( $false
    | spl9_1
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f190,f369])).

fof(f369,plain,
    ( ~ r2_hidden(sK4,sK5)
    | spl9_1 ),
    inference(resolution,[],[f140,f210])).

fof(f210,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(X6,k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8)))
      | ~ r2_hidden(X6,X7) ) ),
    inference(resolution,[],[f124,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
              & ~ r2_hidden(sK6(X0,X1,X2),X1) )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( r2_hidden(sK6(X0,X1,X2),X0)
            | r2_hidden(sK6(X0,X1,X2),X1)
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X3,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X0)
            | r2_hidden(X3,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
            & ~ r2_hidden(sK6(X0,X1,X2),X1) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( r2_hidden(sK6(X0,X1,X2),X0)
          | r2_hidden(sK6(X0,X1,X2),X1)
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X3,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X0)
              | r2_hidden(X3,X1)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f124,plain,(
    ! [X0,X1] : sP0(X1,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(equality_resolution,[],[f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f81,f115])).

fof(f115,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f68,f114])).

fof(f114,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f69,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f74,f112])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f91,f111])).

fof(f111,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f92,f110])).

fof(f110,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f93,f94])).

fof(f94,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f93,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f92,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f91,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f74,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f28])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f140,plain,
    ( ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl9_1
  <=> r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f190,plain,
    ( r2_hidden(sK4,sK5)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl9_4
  <=> r2_hidden(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f345,plain,
    ( ~ spl9_1
    | spl9_3
    | ~ spl9_7 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | ~ spl9_1
    | spl9_3
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f343,f185])).

fof(f185,plain,
    ( sK4 != sK5
    | spl9_3 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl9_3
  <=> sK4 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f343,plain,
    ( sK4 = sK5
    | ~ spl9_1
    | ~ spl9_7 ),
    inference(duplicate_literal_removal,[],[f341])).

fof(f341,plain,
    ( sK4 = sK5
    | sK4 = sK5
    | ~ spl9_1
    | ~ spl9_7 ),
    inference(resolution,[],[f339,f207])).

fof(f207,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f83,f127])).

fof(f127,plain,(
    ! [X0,X1] : sP1(X1,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f89,f114])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP1(X1,X0,X2) )
      & ( sP1(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP1(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f30])).

fof(f30,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | X1 = X4
      | ~ r2_hidden(X4,X2)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ( sK7(X0,X1,X2) != X0
              & sK7(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( sK7(X0,X1,X2) = X0
            | sK7(X0,X1,X2) = X1
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f49,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK7(X0,X1,X2) != X0
            & sK7(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( sK7(X0,X1,X2) = X0
          | sK7(X0,X1,X2) = X1
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f339,plain,
    ( r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | ~ spl9_1
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f338,f322])).

fof(f322,plain,
    ( ~ r2_hidden(sK4,sK5)
    | ~ spl9_7 ),
    inference(resolution,[],[f277,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f277,plain,
    ( r1_tarski(sK5,sK4)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl9_7
  <=> r1_tarski(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f338,plain,
    ( r2_hidden(sK4,sK5)
    | r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | ~ spl9_1 ),
    inference(resolution,[],[f208,f139])).

fof(f139,plain,
    ( r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f138])).

fof(f208,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f124,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f310,plain,
    ( spl9_2
    | ~ spl9_4 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f308,f61])).

fof(f61,plain,(
    v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ r1_ordinal1(sK4,sK5)
      | ~ r2_hidden(sK4,k1_ordinal1(sK5)) )
    & ( r1_ordinal1(sK4,sK5)
      | r2_hidden(sK4,k1_ordinal1(sK5)) )
    & v3_ordinal1(sK5)
    & v3_ordinal1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f36,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK4,X1)
            | ~ r2_hidden(sK4,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK4,X1)
            | r2_hidden(sK4,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(sK4,X1)
          | ~ r2_hidden(sK4,k1_ordinal1(X1)) )
        & ( r1_ordinal1(sK4,X1)
          | r2_hidden(sK4,k1_ordinal1(X1)) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(sK4,sK5)
        | ~ r2_hidden(sK4,k1_ordinal1(sK5)) )
      & ( r1_ordinal1(sK4,sK5)
        | r2_hidden(sK4,k1_ordinal1(sK5)) )
      & v3_ordinal1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f308,plain,
    ( ~ v3_ordinal1(sK4)
    | spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f307,f144])).

fof(f144,plain,
    ( ~ r1_ordinal1(sK4,sK5)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl9_2
  <=> r1_ordinal1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f307,plain,
    ( r1_ordinal1(sK4,sK5)
    | ~ v3_ordinal1(sK4)
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f306,f62])).

fof(f62,plain,(
    v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f306,plain,
    ( ~ v3_ordinal1(sK5)
    | r1_ordinal1(sK4,sK5)
    | ~ v3_ordinal1(sK4)
    | ~ spl9_4 ),
    inference(resolution,[],[f190,f166])).

fof(f166,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ v3_ordinal1(X3)
      | r1_ordinal1(X2,X3)
      | ~ v3_ordinal1(X2) ) ),
    inference(resolution,[],[f156,f73])).

fof(f156,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,X3)
      | ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(X2)
      | r1_ordinal1(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,X3)
      | ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(X2)
      | r1_ordinal1(X3,X2)
      | ~ v3_ordinal1(X2)
      | ~ v3_ordinal1(X3) ) ),
    inference(resolution,[],[f71,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f278,plain,
    ( spl9_4
    | spl9_7
    | spl9_3 ),
    inference(avatar_split_clause,[],[f273,f184,f275,f188])).

fof(f273,plain,
    ( r1_tarski(sK5,sK4)
    | r2_hidden(sK4,sK5)
    | spl9_3 ),
    inference(subsumption_resolution,[],[f272,f62])).

fof(f272,plain,
    ( r1_tarski(sK5,sK4)
    | ~ v3_ordinal1(sK5)
    | r2_hidden(sK4,sK5)
    | spl9_3 ),
    inference(subsumption_resolution,[],[f260,f61])).

fof(f260,plain,
    ( r1_tarski(sK5,sK4)
    | ~ v3_ordinal1(sK4)
    | ~ v3_ordinal1(sK5)
    | r2_hidden(sK4,sK5)
    | spl9_3 ),
    inference(extensionality_resolution,[],[f221,f185])).

fof(f221,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0)
      | X0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f220])).

fof(f220,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f179,f71])).

fof(f179,plain,(
    ! [X2,X1] :
      ( r1_ordinal1(X1,X2)
      | X1 = X2
      | ~ v3_ordinal1(X2)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X2,X1) ) ),
    inference(duplicate_literal_removal,[],[f176])).

fof(f176,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | X1 = X2
      | ~ v3_ordinal1(X2)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X2)
      | r1_ordinal1(X1,X2)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f67,f166])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r2_hidden(X0,X1)
      | X0 = X1
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

% (27564)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
fof(f15,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f248,plain,
    ( spl9_2
    | ~ spl9_3 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f245,f61])).

fof(f245,plain,
    ( ~ v3_ordinal1(sK4)
    | spl9_2
    | ~ spl9_3 ),
    inference(resolution,[],[f240,f150])).

fof(f150,plain,(
    ! [X0] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(duplicate_literal_removal,[],[f149])).

fof(f149,plain,(
    ! [X0] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(factoring,[],[f70])).

fof(f240,plain,
    ( ~ r1_ordinal1(sK4,sK4)
    | spl9_2
    | ~ spl9_3 ),
    inference(forward_demodulation,[],[f144,f186])).

fof(f186,plain,
    ( sK4 = sK5
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f184])).

fof(f239,plain,
    ( spl9_1
    | ~ spl9_3 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | spl9_1
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f235,f168])).

fof(f168,plain,(
    ! [X0,X1] : r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(resolution,[],[f127,f126])).

fof(f126,plain,(
    ! [X4,X2,X0] :
      ( ~ sP1(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f235,plain,
    ( ~ r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | spl9_1
    | ~ spl9_3 ),
    inference(resolution,[],[f229,f209])).

fof(f209,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(X3,k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X4)))
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f124,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f229,plain,
    ( ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | spl9_1
    | ~ spl9_3 ),
    inference(forward_demodulation,[],[f140,f186])).

fof(f194,plain,
    ( spl9_3
    | spl9_4
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f193,f142,f188,f184])).

fof(f193,plain,
    ( r2_hidden(sK4,sK5)
    | sK4 = sK5
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f192,f62])).

fof(f192,plain,
    ( r2_hidden(sK4,sK5)
    | sK4 = sK5
    | ~ v3_ordinal1(sK5)
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f174,f61])).

fof(f174,plain,
    ( r2_hidden(sK4,sK5)
    | sK4 = sK5
    | ~ v3_ordinal1(sK4)
    | ~ v3_ordinal1(sK5)
    | ~ spl9_2 ),
    inference(resolution,[],[f67,f161])).

fof(f161,plain,
    ( ~ r2_hidden(sK5,sK4)
    | ~ spl9_2 ),
    inference(resolution,[],[f159,f73])).

fof(f159,plain,
    ( r1_tarski(sK4,sK5)
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f158,f61])).

fof(f158,plain,
    ( r1_tarski(sK4,sK5)
    | ~ v3_ordinal1(sK4)
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f151,f62])).

fof(f151,plain,
    ( r1_tarski(sK4,sK5)
    | ~ v3_ordinal1(sK5)
    | ~ v3_ordinal1(sK4)
    | ~ spl9_2 ),
    inference(resolution,[],[f71,f143])).

fof(f143,plain,
    ( r1_ordinal1(sK4,sK5)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f142])).

fof(f146,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f119,f142,f138])).

fof(f119,plain,
    ( r1_ordinal1(sK4,sK5)
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(definition_unfolding,[],[f63,f117])).

fof(f117,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f66,f115,f116])).

fof(f116,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f65,f114])).

fof(f65,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f66,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f63,plain,
    ( r1_ordinal1(sK4,sK5)
    | r2_hidden(sK4,k1_ordinal1(sK5)) ),
    inference(cnf_transformation,[],[f39])).

fof(f145,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f118,f142,f138])).

fof(f118,plain,
    ( ~ r1_ordinal1(sK4,sK5)
    | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(definition_unfolding,[],[f64,f117])).

fof(f64,plain,
    ( ~ r1_ordinal1(sK4,sK5)
    | ~ r2_hidden(sK4,k1_ordinal1(sK5)) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:33:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 1.23/0.53  % (27567)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.23/0.53  % (27559)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.23/0.53  % (27567)Refutation not found, incomplete strategy% (27567)------------------------------
% 1.23/0.53  % (27567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (27567)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  
% 1.23/0.53  % (27567)Memory used [KB]: 1791
% 1.23/0.53  % (27567)Time elapsed: 0.065 s
% 1.23/0.53  % (27567)------------------------------
% 1.23/0.53  % (27567)------------------------------
% 1.23/0.54  % (27565)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.38/0.54  % (27553)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.38/0.54  % (27555)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.38/0.54  % (27574)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.38/0.54  % (27559)Refutation found. Thanks to Tanya!
% 1.38/0.54  % SZS status Theorem for theBenchmark
% 1.38/0.54  % SZS output start Proof for theBenchmark
% 1.38/0.54  fof(f407,plain,(
% 1.38/0.54    $false),
% 1.38/0.54    inference(avatar_sat_refutation,[],[f145,f146,f194,f239,f248,f278,f310,f345,f406])).
% 1.38/0.54  % (27580)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.38/0.54  fof(f406,plain,(
% 1.38/0.54    spl9_1 | ~spl9_4),
% 1.38/0.54    inference(avatar_contradiction_clause,[],[f405])).
% 1.38/0.54  fof(f405,plain,(
% 1.38/0.54    $false | (spl9_1 | ~spl9_4)),
% 1.38/0.54    inference(subsumption_resolution,[],[f190,f369])).
% 1.38/0.54  fof(f369,plain,(
% 1.38/0.54    ~r2_hidden(sK4,sK5) | spl9_1),
% 1.38/0.54    inference(resolution,[],[f140,f210])).
% 1.38/0.54  fof(f210,plain,(
% 1.38/0.54    ( ! [X6,X8,X7] : (r2_hidden(X6,k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8))) | ~r2_hidden(X6,X7)) )),
% 1.38/0.54    inference(resolution,[],[f124,f76])).
% 1.38/0.54  fof(f76,plain,(
% 1.38/0.54    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X1) | r2_hidden(X4,X2)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f45])).
% 1.38/0.54  fof(f45,plain,(
% 1.38/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((~r2_hidden(sK6(X0,X1,X2),X0) & ~r2_hidden(sK6(X0,X1,X2),X1)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.38/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).
% 1.38/0.54  fof(f44,plain,(
% 1.38/0.54    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2))) => (((~r2_hidden(sK6(X0,X1,X2),X0) & ~r2_hidden(sK6(X0,X1,X2),X1)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f43,plain,(
% 1.38/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.38/0.54    inference(rectify,[],[f42])).
% 1.38/0.54  fof(f42,plain,(
% 1.38/0.54    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.38/0.54    inference(flattening,[],[f41])).
% 1.38/0.54  fof(f41,plain,(
% 1.38/0.54    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.38/0.54    inference(nnf_transformation,[],[f28])).
% 1.38/0.54  fof(f28,plain,(
% 1.38/0.54    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.38/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.38/0.54  fof(f124,plain,(
% 1.38/0.54    ( ! [X0,X1] : (sP0(X1,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.38/0.54    inference(equality_resolution,[],[f121])).
% 1.38/0.54  fof(f121,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 1.38/0.54    inference(definition_unfolding,[],[f81,f115])).
% 1.38/0.54  fof(f115,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.38/0.54    inference(definition_unfolding,[],[f68,f114])).
% 1.38/0.54  fof(f114,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.38/0.54    inference(definition_unfolding,[],[f69,f113])).
% 1.38/0.54  fof(f113,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.38/0.54    inference(definition_unfolding,[],[f74,f112])).
% 1.38/0.54  fof(f112,plain,(
% 1.38/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.38/0.54    inference(definition_unfolding,[],[f91,f111])).
% 1.38/0.54  fof(f111,plain,(
% 1.38/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.38/0.54    inference(definition_unfolding,[],[f92,f110])).
% 1.38/0.54  fof(f110,plain,(
% 1.38/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.38/0.54    inference(definition_unfolding,[],[f93,f94])).
% 1.38/0.54  fof(f94,plain,(
% 1.38/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f9])).
% 1.38/0.54  fof(f9,axiom,(
% 1.38/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.38/0.54  fof(f93,plain,(
% 1.38/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f8])).
% 1.38/0.54  fof(f8,axiom,(
% 1.38/0.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.38/0.54  fof(f92,plain,(
% 1.38/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f7])).
% 1.38/0.54  fof(f7,axiom,(
% 1.38/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.38/0.54  fof(f91,plain,(
% 1.38/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f6])).
% 1.38/0.54  fof(f6,axiom,(
% 1.38/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.38/0.54  fof(f74,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f5])).
% 1.38/0.54  fof(f5,axiom,(
% 1.38/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.38/0.54  fof(f69,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f4])).
% 1.38/0.54  fof(f4,axiom,(
% 1.38/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.38/0.54  fof(f68,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f10])).
% 1.38/0.54  fof(f10,axiom,(
% 1.38/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.38/0.54  fof(f81,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.38/0.54    inference(cnf_transformation,[],[f46])).
% 1.38/0.54  fof(f46,plain,(
% 1.38/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2))),
% 1.38/0.54    inference(nnf_transformation,[],[f29])).
% 1.38/0.54  fof(f29,plain,(
% 1.38/0.54    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.38/0.54    inference(definition_folding,[],[f1,f28])).
% 1.38/0.54  fof(f1,axiom,(
% 1.38/0.54    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.38/0.54  fof(f140,plain,(
% 1.38/0.54    ~r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) | spl9_1),
% 1.38/0.54    inference(avatar_component_clause,[],[f138])).
% 1.38/0.54  fof(f138,plain,(
% 1.38/0.54    spl9_1 <=> r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.38/0.54  fof(f190,plain,(
% 1.38/0.54    r2_hidden(sK4,sK5) | ~spl9_4),
% 1.38/0.54    inference(avatar_component_clause,[],[f188])).
% 1.38/0.54  fof(f188,plain,(
% 1.38/0.54    spl9_4 <=> r2_hidden(sK4,sK5)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.38/0.54  fof(f345,plain,(
% 1.38/0.54    ~spl9_1 | spl9_3 | ~spl9_7),
% 1.38/0.54    inference(avatar_contradiction_clause,[],[f344])).
% 1.38/0.54  fof(f344,plain,(
% 1.38/0.54    $false | (~spl9_1 | spl9_3 | ~spl9_7)),
% 1.38/0.54    inference(subsumption_resolution,[],[f343,f185])).
% 1.38/0.54  fof(f185,plain,(
% 1.38/0.54    sK4 != sK5 | spl9_3),
% 1.38/0.54    inference(avatar_component_clause,[],[f184])).
% 1.38/0.54  fof(f184,plain,(
% 1.38/0.54    spl9_3 <=> sK4 = sK5),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.38/0.54  fof(f343,plain,(
% 1.38/0.54    sK4 = sK5 | (~spl9_1 | ~spl9_7)),
% 1.38/0.54    inference(duplicate_literal_removal,[],[f341])).
% 1.38/0.54  fof(f341,plain,(
% 1.38/0.54    sK4 = sK5 | sK4 = sK5 | (~spl9_1 | ~spl9_7)),
% 1.38/0.54    inference(resolution,[],[f339,f207])).
% 1.38/0.54  fof(f207,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)) | X0 = X1 | X1 = X2) )),
% 1.38/0.54    inference(resolution,[],[f83,f127])).
% 1.38/0.54  fof(f127,plain,(
% 1.38/0.54    ( ! [X0,X1] : (sP1(X1,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.38/0.54    inference(equality_resolution,[],[f123])).
% 1.38/0.54  fof(f123,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 1.38/0.54    inference(definition_unfolding,[],[f89,f114])).
% 1.38/0.54  fof(f89,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 1.38/0.54    inference(cnf_transformation,[],[f52])).
% 1.38/0.54  fof(f52,plain,(
% 1.38/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 1.38/0.54    inference(nnf_transformation,[],[f31])).
% 1.38/0.54  fof(f31,plain,(
% 1.38/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP1(X1,X0,X2))),
% 1.38/0.54    inference(definition_folding,[],[f2,f30])).
% 1.38/0.54  fof(f30,plain,(
% 1.38/0.54    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.38/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.38/0.54  fof(f2,axiom,(
% 1.38/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.38/0.54  fof(f83,plain,(
% 1.38/0.54    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 1.38/0.54    inference(cnf_transformation,[],[f51])).
% 1.38/0.54  fof(f51,plain,(
% 1.38/0.54    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (((sK7(X0,X1,X2) != X0 & sK7(X0,X1,X2) != X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sK7(X0,X1,X2) = X0 | sK7(X0,X1,X2) = X1 | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.38/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f49,f50])).
% 1.38/0.54  fof(f50,plain,(
% 1.38/0.54    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK7(X0,X1,X2) != X0 & sK7(X0,X1,X2) != X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sK7(X0,X1,X2) = X0 | sK7(X0,X1,X2) = X1 | r2_hidden(sK7(X0,X1,X2),X2))))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f49,plain,(
% 1.38/0.54    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.38/0.54    inference(rectify,[],[f48])).
% 1.38/0.54  fof(f48,plain,(
% 1.38/0.54    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 1.38/0.54    inference(flattening,[],[f47])).
% 1.38/0.54  fof(f47,plain,(
% 1.38/0.54    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 1.38/0.54    inference(nnf_transformation,[],[f30])).
% 1.38/0.54  fof(f339,plain,(
% 1.38/0.54    r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) | (~spl9_1 | ~spl9_7)),
% 1.38/0.54    inference(subsumption_resolution,[],[f338,f322])).
% 1.38/0.54  fof(f322,plain,(
% 1.38/0.54    ~r2_hidden(sK4,sK5) | ~spl9_7),
% 1.38/0.54    inference(resolution,[],[f277,f73])).
% 1.38/0.54  fof(f73,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f26])).
% 1.38/0.54  fof(f26,plain,(
% 1.38/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.38/0.54    inference(ennf_transformation,[],[f16])).
% 1.38/0.54  fof(f16,axiom,(
% 1.38/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.38/0.54  fof(f277,plain,(
% 1.38/0.54    r1_tarski(sK5,sK4) | ~spl9_7),
% 1.38/0.54    inference(avatar_component_clause,[],[f275])).
% 1.38/0.54  fof(f275,plain,(
% 1.38/0.54    spl9_7 <=> r1_tarski(sK5,sK4)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 1.38/0.54  fof(f338,plain,(
% 1.38/0.54    r2_hidden(sK4,sK5) | r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) | ~spl9_1),
% 1.38/0.54    inference(resolution,[],[f208,f139])).
% 1.38/0.54  fof(f139,plain,(
% 1.38/0.54    r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) | ~spl9_1),
% 1.38/0.54    inference(avatar_component_clause,[],[f138])).
% 1.38/0.54  fof(f208,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 1.38/0.54    inference(resolution,[],[f124,f75])).
% 1.38/0.54  fof(f75,plain,(
% 1.38/0.54    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | r2_hidden(X4,X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f45])).
% 1.38/0.54  fof(f310,plain,(
% 1.38/0.54    spl9_2 | ~spl9_4),
% 1.38/0.54    inference(avatar_contradiction_clause,[],[f309])).
% 1.38/0.54  fof(f309,plain,(
% 1.38/0.54    $false | (spl9_2 | ~spl9_4)),
% 1.38/0.54    inference(subsumption_resolution,[],[f308,f61])).
% 1.38/0.54  fof(f61,plain,(
% 1.38/0.54    v3_ordinal1(sK4)),
% 1.38/0.54    inference(cnf_transformation,[],[f39])).
% 1.38/0.54  fof(f39,plain,(
% 1.38/0.54    ((~r1_ordinal1(sK4,sK5) | ~r2_hidden(sK4,k1_ordinal1(sK5))) & (r1_ordinal1(sK4,sK5) | r2_hidden(sK4,k1_ordinal1(sK5))) & v3_ordinal1(sK5)) & v3_ordinal1(sK4)),
% 1.38/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f36,f38,f37])).
% 1.38/0.54  fof(f37,plain,(
% 1.38/0.54    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK4,X1) | ~r2_hidden(sK4,k1_ordinal1(X1))) & (r1_ordinal1(sK4,X1) | r2_hidden(sK4,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK4))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f38,plain,(
% 1.38/0.54    ? [X1] : ((~r1_ordinal1(sK4,X1) | ~r2_hidden(sK4,k1_ordinal1(X1))) & (r1_ordinal1(sK4,X1) | r2_hidden(sK4,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(sK4,sK5) | ~r2_hidden(sK4,k1_ordinal1(sK5))) & (r1_ordinal1(sK4,sK5) | r2_hidden(sK4,k1_ordinal1(sK5))) & v3_ordinal1(sK5))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f36,plain,(
% 1.38/0.54    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.38/0.54    inference(flattening,[],[f35])).
% 1.38/0.54  fof(f35,plain,(
% 1.38/0.54    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.38/0.54    inference(nnf_transformation,[],[f19])).
% 1.38/0.54  fof(f19,plain,(
% 1.38/0.54    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.38/0.54    inference(ennf_transformation,[],[f18])).
% 1.38/0.54  fof(f18,negated_conjecture,(
% 1.38/0.54    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.38/0.54    inference(negated_conjecture,[],[f17])).
% 1.38/0.54  fof(f17,conjecture,(
% 1.38/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 1.38/0.54  fof(f308,plain,(
% 1.38/0.54    ~v3_ordinal1(sK4) | (spl9_2 | ~spl9_4)),
% 1.38/0.54    inference(subsumption_resolution,[],[f307,f144])).
% 1.38/0.54  fof(f144,plain,(
% 1.38/0.54    ~r1_ordinal1(sK4,sK5) | spl9_2),
% 1.38/0.54    inference(avatar_component_clause,[],[f142])).
% 1.38/0.54  fof(f142,plain,(
% 1.38/0.54    spl9_2 <=> r1_ordinal1(sK4,sK5)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.38/0.54  fof(f307,plain,(
% 1.38/0.54    r1_ordinal1(sK4,sK5) | ~v3_ordinal1(sK4) | ~spl9_4),
% 1.38/0.54    inference(subsumption_resolution,[],[f306,f62])).
% 1.38/0.54  fof(f62,plain,(
% 1.38/0.54    v3_ordinal1(sK5)),
% 1.38/0.54    inference(cnf_transformation,[],[f39])).
% 1.38/0.54  fof(f306,plain,(
% 1.38/0.54    ~v3_ordinal1(sK5) | r1_ordinal1(sK4,sK5) | ~v3_ordinal1(sK4) | ~spl9_4),
% 1.38/0.54    inference(resolution,[],[f190,f166])).
% 1.38/0.54  fof(f166,plain,(
% 1.38/0.54    ( ! [X2,X3] : (~r2_hidden(X2,X3) | ~v3_ordinal1(X3) | r1_ordinal1(X2,X3) | ~v3_ordinal1(X2)) )),
% 1.38/0.54    inference(resolution,[],[f156,f73])).
% 1.38/0.54  fof(f156,plain,(
% 1.38/0.54    ( ! [X2,X3] : (r1_tarski(X2,X3) | ~v3_ordinal1(X3) | ~v3_ordinal1(X2) | r1_ordinal1(X3,X2)) )),
% 1.38/0.54    inference(duplicate_literal_removal,[],[f153])).
% 1.38/0.54  fof(f153,plain,(
% 1.38/0.54    ( ! [X2,X3] : (r1_tarski(X2,X3) | ~v3_ordinal1(X3) | ~v3_ordinal1(X2) | r1_ordinal1(X3,X2) | ~v3_ordinal1(X2) | ~v3_ordinal1(X3)) )),
% 1.38/0.54    inference(resolution,[],[f71,f70])).
% 1.38/0.54  fof(f70,plain,(
% 1.38/0.54    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f23])).
% 1.38/0.54  fof(f23,plain,(
% 1.38/0.54    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.38/0.54    inference(flattening,[],[f22])).
% 1.38/0.54  fof(f22,plain,(
% 1.38/0.54    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.38/0.54    inference(ennf_transformation,[],[f12])).
% 1.38/0.54  fof(f12,axiom,(
% 1.38/0.54    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 1.38/0.54  fof(f71,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f40])).
% 1.38/0.54  fof(f40,plain,(
% 1.38/0.54    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.38/0.54    inference(nnf_transformation,[],[f25])).
% 1.38/0.54  fof(f25,plain,(
% 1.38/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.38/0.54    inference(flattening,[],[f24])).
% 1.38/0.54  fof(f24,plain,(
% 1.38/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.38/0.54    inference(ennf_transformation,[],[f14])).
% 1.38/0.54  fof(f14,axiom,(
% 1.38/0.54    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.38/0.54  fof(f278,plain,(
% 1.38/0.54    spl9_4 | spl9_7 | spl9_3),
% 1.38/0.54    inference(avatar_split_clause,[],[f273,f184,f275,f188])).
% 1.38/0.54  fof(f273,plain,(
% 1.38/0.54    r1_tarski(sK5,sK4) | r2_hidden(sK4,sK5) | spl9_3),
% 1.38/0.54    inference(subsumption_resolution,[],[f272,f62])).
% 1.38/0.54  fof(f272,plain,(
% 1.38/0.54    r1_tarski(sK5,sK4) | ~v3_ordinal1(sK5) | r2_hidden(sK4,sK5) | spl9_3),
% 1.38/0.54    inference(subsumption_resolution,[],[f260,f61])).
% 1.38/0.54  fof(f260,plain,(
% 1.38/0.54    r1_tarski(sK5,sK4) | ~v3_ordinal1(sK4) | ~v3_ordinal1(sK5) | r2_hidden(sK4,sK5) | spl9_3),
% 1.38/0.54    inference(extensionality_resolution,[],[f221,f185])).
% 1.38/0.54  fof(f221,plain,(
% 1.38/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0) | X0 = X1) )),
% 1.38/0.54    inference(duplicate_literal_removal,[],[f220])).
% 1.38/0.54  fof(f220,plain,(
% 1.38/0.54    ( ! [X0,X1] : (X0 = X1 | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.38/0.54    inference(resolution,[],[f179,f71])).
% 1.38/0.54  fof(f179,plain,(
% 1.38/0.54    ( ! [X2,X1] : (r1_ordinal1(X1,X2) | X1 = X2 | ~v3_ordinal1(X2) | ~v3_ordinal1(X1) | r2_hidden(X2,X1)) )),
% 1.38/0.54    inference(duplicate_literal_removal,[],[f176])).
% 1.38/0.54  fof(f176,plain,(
% 1.38/0.54    ( ! [X2,X1] : (r2_hidden(X2,X1) | X1 = X2 | ~v3_ordinal1(X2) | ~v3_ordinal1(X1) | ~v3_ordinal1(X2) | r1_ordinal1(X1,X2) | ~v3_ordinal1(X1)) )),
% 1.38/0.54    inference(resolution,[],[f67,f166])).
% 1.38/0.54  fof(f67,plain,(
% 1.38/0.54    ( ! [X0,X1] : (r2_hidden(X1,X0) | r2_hidden(X0,X1) | X0 = X1 | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f21])).
% 1.38/0.54  fof(f21,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.38/0.54    inference(flattening,[],[f20])).
% 1.38/0.54  fof(f20,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.38/0.54    inference(ennf_transformation,[],[f15])).
% 1.38/0.54  % (27564)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.38/0.54  fof(f15,axiom,(
% 1.38/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 1.38/0.54  fof(f248,plain,(
% 1.38/0.54    spl9_2 | ~spl9_3),
% 1.38/0.54    inference(avatar_contradiction_clause,[],[f247])).
% 1.38/0.54  fof(f247,plain,(
% 1.38/0.54    $false | (spl9_2 | ~spl9_3)),
% 1.38/0.54    inference(subsumption_resolution,[],[f245,f61])).
% 1.38/0.54  fof(f245,plain,(
% 1.38/0.54    ~v3_ordinal1(sK4) | (spl9_2 | ~spl9_3)),
% 1.38/0.54    inference(resolution,[],[f240,f150])).
% 1.38/0.54  fof(f150,plain,(
% 1.38/0.54    ( ! [X0] : (r1_ordinal1(X0,X0) | ~v3_ordinal1(X0)) )),
% 1.38/0.54    inference(duplicate_literal_removal,[],[f149])).
% 1.38/0.54  fof(f149,plain,(
% 1.38/0.54    ( ! [X0] : (r1_ordinal1(X0,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 1.38/0.54    inference(factoring,[],[f70])).
% 1.38/0.54  fof(f240,plain,(
% 1.38/0.54    ~r1_ordinal1(sK4,sK4) | (spl9_2 | ~spl9_3)),
% 1.38/0.54    inference(forward_demodulation,[],[f144,f186])).
% 1.38/0.54  fof(f186,plain,(
% 1.38/0.54    sK4 = sK5 | ~spl9_3),
% 1.38/0.54    inference(avatar_component_clause,[],[f184])).
% 1.38/0.54  fof(f239,plain,(
% 1.38/0.54    spl9_1 | ~spl9_3),
% 1.38/0.54    inference(avatar_contradiction_clause,[],[f238])).
% 1.38/0.54  fof(f238,plain,(
% 1.38/0.54    $false | (spl9_1 | ~spl9_3)),
% 1.38/0.54    inference(subsumption_resolution,[],[f235,f168])).
% 1.38/0.54  fof(f168,plain,(
% 1.38/0.54    ( ! [X0,X1] : (r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.38/0.54    inference(resolution,[],[f127,f126])).
% 1.38/0.54  fof(f126,plain,(
% 1.38/0.54    ( ! [X4,X2,X0] : (~sP1(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 1.38/0.54    inference(equality_resolution,[],[f84])).
% 1.38/0.54  fof(f84,plain,(
% 1.38/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP1(X0,X1,X2)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f51])).
% 1.38/0.54  fof(f235,plain,(
% 1.38/0.54    ~r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) | (spl9_1 | ~spl9_3)),
% 1.38/0.54    inference(resolution,[],[f229,f209])).
% 1.38/0.54  fof(f209,plain,(
% 1.38/0.54    ( ! [X4,X5,X3] : (r2_hidden(X3,k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X4))) | ~r2_hidden(X3,X4)) )),
% 1.38/0.54    inference(resolution,[],[f124,f77])).
% 1.38/0.54  fof(f77,plain,(
% 1.38/0.54    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X0) | r2_hidden(X4,X2)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f45])).
% 1.38/0.54  fof(f229,plain,(
% 1.38/0.54    ~r2_hidden(sK4,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) | (spl9_1 | ~spl9_3)),
% 1.38/0.54    inference(forward_demodulation,[],[f140,f186])).
% 1.38/0.54  fof(f194,plain,(
% 1.38/0.54    spl9_3 | spl9_4 | ~spl9_2),
% 1.38/0.54    inference(avatar_split_clause,[],[f193,f142,f188,f184])).
% 1.38/0.54  fof(f193,plain,(
% 1.38/0.54    r2_hidden(sK4,sK5) | sK4 = sK5 | ~spl9_2),
% 1.38/0.54    inference(subsumption_resolution,[],[f192,f62])).
% 1.38/0.54  fof(f192,plain,(
% 1.38/0.54    r2_hidden(sK4,sK5) | sK4 = sK5 | ~v3_ordinal1(sK5) | ~spl9_2),
% 1.38/0.54    inference(subsumption_resolution,[],[f174,f61])).
% 1.38/0.54  fof(f174,plain,(
% 1.38/0.54    r2_hidden(sK4,sK5) | sK4 = sK5 | ~v3_ordinal1(sK4) | ~v3_ordinal1(sK5) | ~spl9_2),
% 1.38/0.54    inference(resolution,[],[f67,f161])).
% 1.38/0.54  fof(f161,plain,(
% 1.38/0.54    ~r2_hidden(sK5,sK4) | ~spl9_2),
% 1.38/0.54    inference(resolution,[],[f159,f73])).
% 1.38/0.54  fof(f159,plain,(
% 1.38/0.54    r1_tarski(sK4,sK5) | ~spl9_2),
% 1.38/0.54    inference(subsumption_resolution,[],[f158,f61])).
% 1.38/0.54  fof(f158,plain,(
% 1.38/0.54    r1_tarski(sK4,sK5) | ~v3_ordinal1(sK4) | ~spl9_2),
% 1.38/0.54    inference(subsumption_resolution,[],[f151,f62])).
% 1.38/0.54  fof(f151,plain,(
% 1.38/0.54    r1_tarski(sK4,sK5) | ~v3_ordinal1(sK5) | ~v3_ordinal1(sK4) | ~spl9_2),
% 1.38/0.54    inference(resolution,[],[f71,f143])).
% 1.38/0.54  fof(f143,plain,(
% 1.38/0.54    r1_ordinal1(sK4,sK5) | ~spl9_2),
% 1.38/0.54    inference(avatar_component_clause,[],[f142])).
% 1.38/0.54  fof(f146,plain,(
% 1.38/0.54    spl9_1 | spl9_2),
% 1.38/0.54    inference(avatar_split_clause,[],[f119,f142,f138])).
% 1.38/0.54  fof(f119,plain,(
% 1.38/0.54    r1_ordinal1(sK4,sK5) | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))),
% 1.38/0.54    inference(definition_unfolding,[],[f63,f117])).
% 1.38/0.54  fof(f117,plain,(
% 1.38/0.54    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) )),
% 1.38/0.54    inference(definition_unfolding,[],[f66,f115,f116])).
% 1.38/0.54  fof(f116,plain,(
% 1.38/0.54    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.38/0.54    inference(definition_unfolding,[],[f65,f114])).
% 1.38/0.54  fof(f65,plain,(
% 1.38/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f3])).
% 1.38/0.54  fof(f3,axiom,(
% 1.38/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.38/0.54  fof(f66,plain,(
% 1.38/0.54    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f13])).
% 1.38/0.54  fof(f13,axiom,(
% 1.38/0.54    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.38/0.54  fof(f63,plain,(
% 1.38/0.54    r1_ordinal1(sK4,sK5) | r2_hidden(sK4,k1_ordinal1(sK5))),
% 1.38/0.54    inference(cnf_transformation,[],[f39])).
% 1.38/0.54  fof(f145,plain,(
% 1.38/0.54    ~spl9_1 | ~spl9_2),
% 1.38/0.54    inference(avatar_split_clause,[],[f118,f142,f138])).
% 1.38/0.54  fof(f118,plain,(
% 1.38/0.54    ~r1_ordinal1(sK4,sK5) | ~r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))),
% 1.38/0.54    inference(definition_unfolding,[],[f64,f117])).
% 1.38/0.54  fof(f64,plain,(
% 1.38/0.54    ~r1_ordinal1(sK4,sK5) | ~r2_hidden(sK4,k1_ordinal1(sK5))),
% 1.38/0.54    inference(cnf_transformation,[],[f39])).
% 1.38/0.54  % SZS output end Proof for theBenchmark
% 1.38/0.54  % (27559)------------------------------
% 1.38/0.54  % (27559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (27559)Termination reason: Refutation
% 1.38/0.54  
% 1.38/0.54  % (27559)Memory used [KB]: 10874
% 1.38/0.54  % (27559)Time elapsed: 0.085 s
% 1.38/0.54  % (27559)------------------------------
% 1.38/0.54  % (27559)------------------------------
% 1.38/0.54  % (27552)Success in time 0.179 s
%------------------------------------------------------------------------------
