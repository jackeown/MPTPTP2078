%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:07 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 621 expanded)
%              Number of leaves         :   24 ( 193 expanded)
%              Depth                    :   19
%              Number of atoms          :  407 (2358 expanded)
%              Number of equality atoms :  188 (1057 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f577,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f146,f526,f550,f576])).

fof(f576,plain,(
    ~ spl13_1 ),
    inference(avatar_contradiction_clause,[],[f575])).

fof(f575,plain,
    ( $false
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f574,f247])).

fof(f247,plain,(
    ! [X15,X16] : r2_hidden(X16,k1_enumset1(X15,X15,X16)) ),
    inference(trivial_inequality_removal,[],[f246])).

fof(f246,plain,(
    ! [X15,X16] :
      ( k1_xboole_0 != k1_xboole_0
      | r2_hidden(X16,k1_enumset1(X15,X15,X16)) ) ),
    inference(superposition,[],[f120,f233])).

fof(f233,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(duplicate_literal_removal,[],[f226])).

fof(f226,plain,(
    ! [X0] :
      ( k1_xboole_0 = k4_xboole_0(X0,X0)
      | k1_xboole_0 = k4_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f216,f215])).

fof(f215,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK10(k4_xboole_0(X0,X1)),X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f179,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( ~ r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X1,X3,X0] :
      ( ( sP1(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP1(X1,X3,X0) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X1,X3,X0] :
      ( ( sP1(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP1(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X1,X3,X0] :
      ( sP1(X1,X3,X0)
    <=> ( ~ r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f179,plain,(
    ! [X0,X1] :
      ( sP1(X0,sK10(k4_xboole_0(X1,X0)),X1)
      | k1_xboole_0 = k4_xboole_0(X1,X0) ) ),
    inference(resolution,[],[f170,f75])).

fof(f75,plain,(
    ! [X0] :
      ( r2_hidden(sK10(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( sP0(sK10(X0),X0)
        & r2_hidden(sK10(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f25,f39])).

% (5851)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
     => ( sP0(sK10(X0),X0)
        & r2_hidden(sK10(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f20,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ! [X2,X3,X4] :
          ( k3_mcart_1(X2,X3,X4) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | sP1(X2,X0,X1) ) ),
    inference(resolution,[],[f82,f128])).

fof(f128,plain,(
    ! [X0,X1] : sP2(X0,X1,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP2(X0,X1,X2) )
      & ( sP2(X0,X1,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP2(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f27,f26])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP1(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP1(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ~ sP1(X1,sK11(X0,X1,X2),X0)
            | ~ r2_hidden(sK11(X0,X1,X2),X2) )
          & ( sP1(X1,sK11(X0,X1,X2),X0)
            | r2_hidden(sK11(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X1,X4,X0) )
            & ( sP1(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP1(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP1(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP1(X1,sK11(X0,X1,X2),X0)
          | ~ r2_hidden(sK11(X0,X1,X2),X2) )
        & ( sP1(X1,sK11(X0,X1,X2),X0)
          | r2_hidden(sK11(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X1,X4,X0) )
            & ( sP1(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP1(X1,X3,X0) )
            & ( sP1(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f216,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK10(k4_xboole_0(X2,X3)),X2)
      | k1_xboole_0 = k4_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f179,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(k1_enumset1(X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f95,f77])).

fof(f77,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f574,plain,
    ( ~ r2_hidden(sK9,k1_enumset1(sK9,sK9,sK9))
    | ~ spl13_1 ),
    inference(resolution,[],[f564,f354])).

fof(f354,plain,(
    ! [X6] : sP0(X6,k1_enumset1(X6,X6,X6)) ),
    inference(subsumption_resolution,[],[f349,f205])).

fof(f205,plain,(
    ! [X0,X1] : k1_xboole_0 != k1_enumset1(X0,X0,X1) ),
    inference(subsumption_resolution,[],[f203,f151])).

fof(f151,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f129,f68])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f129,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f92,f112])).

fof(f112,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f70,f77])).

fof(f70,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f203,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_enumset1(X0,X0,X1)
      | r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f120,f69])).

fof(f69,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f349,plain,(
    ! [X6] :
      ( sP0(X6,k1_enumset1(X6,X6,X6))
      | k1_xboole_0 = k1_enumset1(X6,X6,X6) ) ),
    inference(superposition,[],[f76,f344])).

fof(f344,plain,(
    ! [X0] : sK10(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(subsumption_resolution,[],[f337,f205])).

fof(f337,plain,(
    ! [X0] :
      ( sK10(k1_enumset1(X0,X0,X0)) = X0
      | k1_xboole_0 = k1_enumset1(X0,X0,X0) ) ),
    inference(resolution,[],[f336,f75])).

fof(f336,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X7,k1_enumset1(X6,X6,X6))
      | X6 = X7 ) ),
    inference(subsumption_resolution,[],[f335,f151])).

fof(f335,plain,(
    ! [X6,X7] :
      ( r2_hidden(X7,k1_xboole_0)
      | X6 = X7
      | ~ r2_hidden(X7,k1_enumset1(X6,X6,X6)) ) ),
    inference(superposition,[],[f116,f233])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f93,f112])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f76,plain,(
    ! [X0] :
      ( sP0(sK10(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f564,plain,
    ( ! [X0] :
        ( ~ sP0(sK9,X0)
        | ~ r2_hidden(sK9,X0) )
    | ~ spl13_1 ),
    inference(superposition,[],[f127,f559])).

fof(f559,plain,
    ( sK9 = k4_tarski(k4_tarski(sK9,k6_mcart_1(sK6,sK7,sK8,sK9)),k7_mcart_1(sK6,sK7,sK8,sK9))
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f558,f63])).

fof(f63,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( sK9 = k7_mcart_1(sK6,sK7,sK8,sK9)
      | sK9 = k6_mcart_1(sK6,sK7,sK8,sK9)
      | sK9 = k5_mcart_1(sK6,sK7,sK8,sK9) )
    & m1_subset_1(sK9,k3_zfmisc_1(sK6,sK7,sK8))
    & k1_xboole_0 != sK8
    & k1_xboole_0 != sK7
    & k1_xboole_0 != sK6 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f18,f35,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( k7_mcart_1(X0,X1,X2,X3) = X3
              | k6_mcart_1(X0,X1,X2,X3) = X3
              | k5_mcart_1(X0,X1,X2,X3) = X3 )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X3] :
          ( ( k7_mcart_1(sK6,sK7,sK8,X3) = X3
            | k6_mcart_1(sK6,sK7,sK8,X3) = X3
            | k5_mcart_1(sK6,sK7,sK8,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(sK6,sK7,sK8)) )
      & k1_xboole_0 != sK8
      & k1_xboole_0 != sK7
      & k1_xboole_0 != sK6 ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X3] :
        ( ( k7_mcart_1(sK6,sK7,sK8,X3) = X3
          | k6_mcart_1(sK6,sK7,sK8,X3) = X3
          | k5_mcart_1(sK6,sK7,sK8,X3) = X3 )
        & m1_subset_1(X3,k3_zfmisc_1(sK6,sK7,sK8)) )
   => ( ( sK9 = k7_mcart_1(sK6,sK7,sK8,sK9)
        | sK9 = k6_mcart_1(sK6,sK7,sK8,sK9)
        | sK9 = k5_mcart_1(sK6,sK7,sK8,sK9) )
      & m1_subset_1(sK9,k3_zfmisc_1(sK6,sK7,sK8)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) != X3
                & k6_mcart_1(X0,X1,X2,X3) != X3
                & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).

fof(f558,plain,
    ( sK9 = k4_tarski(k4_tarski(sK9,k6_mcart_1(sK6,sK7,sK8,sK9)),k7_mcart_1(sK6,sK7,sK8,sK9))
    | k1_xboole_0 = sK6
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f557,f64])).

fof(f64,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f36])).

fof(f557,plain,
    ( sK9 = k4_tarski(k4_tarski(sK9,k6_mcart_1(sK6,sK7,sK8,sK9)),k7_mcart_1(sK6,sK7,sK8,sK9))
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f556,f65])).

fof(f65,plain,(
    k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f36])).

fof(f556,plain,
    ( sK9 = k4_tarski(k4_tarski(sK9,k6_mcart_1(sK6,sK7,sK8,sK9)),k7_mcart_1(sK6,sK7,sK8,sK9))
    | k1_xboole_0 = sK8
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f553,f113])).

fof(f113,plain,(
    m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) ),
    inference(definition_unfolding,[],[f66,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f66,plain,(
    m1_subset_1(sK9,k3_zfmisc_1(sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f36])).

fof(f553,plain,
    ( sK9 = k4_tarski(k4_tarski(sK9,k6_mcart_1(sK6,sK7,sK8,sK9)),k7_mcart_1(sK6,sK7,sK8,sK9))
    | ~ m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8))
    | k1_xboole_0 = sK8
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | ~ spl13_1 ),
    inference(superposition,[],[f122,f137])).

fof(f137,plain,
    ( sK9 = k5_mcart_1(sK6,sK7,sK8,sK9)
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl13_1
  <=> sK9 = k5_mcart_1(sK6,sK7,sK8,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f122,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f97,f80,f81])).

fof(f80,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f127,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ sP0(k4_tarski(k4_tarski(X2,X3),X4),X1)
      | ~ r2_hidden(X2,X1) ) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != X0
      | ~ r2_hidden(X2,X1)
      | ~ sP0(X0,X1) ) ),
    inference(definition_unfolding,[],[f73,f80])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_mcart_1(X2,X3,X4) != X0
      | ~ r2_hidden(X2,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2,X3,X4] :
          ( k3_mcart_1(X2,X3,X4) != X0
          | ( ~ r2_hidden(X3,X1)
            & ~ r2_hidden(X2,X1) ) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f37])).

% (5863)Refutation not found, incomplete strategy% (5863)------------------------------
% (5863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f37,plain,(
    ! [X1,X0] :
      ( ! [X2,X3,X4] :
          ( k3_mcart_1(X2,X3,X4) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP0(X1,X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f550,plain,(
    ~ spl13_2 ),
    inference(avatar_contradiction_clause,[],[f549])).

% (5863)Termination reason: Refutation not found, incomplete strategy

fof(f549,plain,
    ( $false
    | ~ spl13_2 ),
    inference(subsumption_resolution,[],[f548,f247])).

fof(f548,plain,
    ( ~ r2_hidden(sK9,k1_enumset1(sK9,sK9,sK9))
    | ~ spl13_2 ),
    inference(resolution,[],[f539,f354])).

% (5863)Memory used [KB]: 11001
% (5863)Time elapsed: 0.124 s
fof(f539,plain,
    ( ! [X1] :
        ( ~ sP0(sK9,X1)
        | ~ r2_hidden(sK9,X1) )
    | ~ spl13_2 ),
    inference(superposition,[],[f126,f533])).

% (5863)------------------------------
% (5863)------------------------------
fof(f533,plain,
    ( sK9 = k4_tarski(k4_tarski(k5_mcart_1(sK6,sK7,sK8,sK9),sK9),k7_mcart_1(sK6,sK7,sK8,sK9))
    | ~ spl13_2 ),
    inference(subsumption_resolution,[],[f532,f63])).

fof(f532,plain,
    ( sK9 = k4_tarski(k4_tarski(k5_mcart_1(sK6,sK7,sK8,sK9),sK9),k7_mcart_1(sK6,sK7,sK8,sK9))
    | k1_xboole_0 = sK6
    | ~ spl13_2 ),
    inference(subsumption_resolution,[],[f531,f64])).

fof(f531,plain,
    ( sK9 = k4_tarski(k4_tarski(k5_mcart_1(sK6,sK7,sK8,sK9),sK9),k7_mcart_1(sK6,sK7,sK8,sK9))
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | ~ spl13_2 ),
    inference(subsumption_resolution,[],[f530,f65])).

fof(f530,plain,
    ( sK9 = k4_tarski(k4_tarski(k5_mcart_1(sK6,sK7,sK8,sK9),sK9),k7_mcart_1(sK6,sK7,sK8,sK9))
    | k1_xboole_0 = sK8
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | ~ spl13_2 ),
    inference(subsumption_resolution,[],[f528,f113])).

fof(f528,plain,
    ( sK9 = k4_tarski(k4_tarski(k5_mcart_1(sK6,sK7,sK8,sK9),sK9),k7_mcart_1(sK6,sK7,sK8,sK9))
    | ~ m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8))
    | k1_xboole_0 = sK8
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | ~ spl13_2 ),
    inference(superposition,[],[f122,f141])).

fof(f141,plain,
    ( sK9 = k6_mcart_1(sK6,sK7,sK8,sK9)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl13_2
  <=> sK9 = k6_mcart_1(sK6,sK7,sK8,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f126,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ sP0(k4_tarski(k4_tarski(X2,X3),X4),X1)
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != X0
      | ~ r2_hidden(X3,X1)
      | ~ sP0(X0,X1) ) ),
    inference(definition_unfolding,[],[f74,f80])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_mcart_1(X2,X3,X4) != X0
      | ~ r2_hidden(X3,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f526,plain,(
    ~ spl13_3 ),
    inference(avatar_contradiction_clause,[],[f525])).

fof(f525,plain,
    ( $false
    | ~ spl13_3 ),
    inference(subsumption_resolution,[],[f524,f63])).

fof(f524,plain,
    ( k1_xboole_0 = sK6
    | ~ spl13_3 ),
    inference(subsumption_resolution,[],[f523,f64])).

fof(f523,plain,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | ~ spl13_3 ),
    inference(subsumption_resolution,[],[f522,f65])).

fof(f522,plain,
    ( k1_xboole_0 = sK8
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | ~ spl13_3 ),
    inference(subsumption_resolution,[],[f521,f113])).

fof(f521,plain,
    ( ~ m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8))
    | k1_xboole_0 = sK8
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | ~ spl13_3 ),
    inference(subsumption_resolution,[],[f509,f149])).

fof(f149,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != X2 ),
    inference(forward_demodulation,[],[f124,f79])).

fof(f79,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f124,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f509,plain,
    ( sK9 = k4_tarski(k4_tarski(k5_mcart_1(sK6,sK7,sK8,sK9),k6_mcart_1(sK6,sK7,sK8,sK9)),sK9)
    | ~ m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8))
    | k1_xboole_0 = sK8
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | ~ spl13_3 ),
    inference(superposition,[],[f122,f145])).

fof(f145,plain,
    ( sK9 = k7_mcart_1(sK6,sK7,sK8,sK9)
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl13_3
  <=> sK9 = k7_mcart_1(sK6,sK7,sK8,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f146,plain,
    ( spl13_1
    | spl13_2
    | spl13_3 ),
    inference(avatar_split_clause,[],[f67,f143,f139,f135])).

fof(f67,plain,
    ( sK9 = k7_mcart_1(sK6,sK7,sK8,sK9)
    | sK9 = k6_mcart_1(sK6,sK7,sK8,sK9)
    | sK9 = k5_mcart_1(sK6,sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:33:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (5846)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (5854)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.31/0.55  % (5844)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.31/0.55  % (5845)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.31/0.56  % (5856)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.59/0.57  % (5848)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.59/0.57  % (5865)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.59/0.58  % (5870)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.59/0.58  % (5868)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.59/0.58  % (5855)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.59/0.58  % (5869)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.59/0.58  % (5863)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.59/0.59  % (5841)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.59/0.59  % (5860)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.59/0.59  % (5861)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.59/0.59  % (5864)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.59/0.59  % (5861)Refutation not found, incomplete strategy% (5861)------------------------------
% 1.59/0.59  % (5861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.59  % (5861)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.59  
% 1.59/0.59  % (5861)Memory used [KB]: 10746
% 1.59/0.59  % (5861)Time elapsed: 0.176 s
% 1.59/0.59  % (5861)------------------------------
% 1.59/0.59  % (5861)------------------------------
% 1.59/0.59  % (5853)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.59/0.59  % (5862)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.59/0.59  % (5847)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.59/0.59  % (5862)Refutation not found, incomplete strategy% (5862)------------------------------
% 1.59/0.59  % (5862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.59  % (5862)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.59  
% 1.59/0.59  % (5862)Memory used [KB]: 1791
% 1.59/0.59  % (5862)Time elapsed: 0.186 s
% 1.59/0.59  % (5862)------------------------------
% 1.59/0.59  % (5862)------------------------------
% 1.59/0.59  % (5852)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.59/0.60  % (5852)Refutation not found, incomplete strategy% (5852)------------------------------
% 1.59/0.60  % (5852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.60  % (5852)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.60  
% 1.59/0.60  % (5852)Memory used [KB]: 10618
% 1.59/0.60  % (5852)Time elapsed: 0.189 s
% 1.59/0.60  % (5852)------------------------------
% 1.59/0.60  % (5852)------------------------------
% 1.59/0.61  % (5864)Refutation not found, incomplete strategy% (5864)------------------------------
% 1.59/0.61  % (5864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.61  % (5864)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.61  
% 1.59/0.61  % (5864)Memory used [KB]: 1791
% 1.59/0.61  % (5864)Time elapsed: 0.174 s
% 1.59/0.61  % (5864)------------------------------
% 1.59/0.61  % (5864)------------------------------
% 1.59/0.62  % (5843)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.59/0.62  % (5842)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.59/0.62  % (5843)Refutation not found, incomplete strategy% (5843)------------------------------
% 1.59/0.62  % (5843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.62  % (5843)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.62  
% 1.59/0.62  % (5843)Memory used [KB]: 10746
% 1.59/0.62  % (5843)Time elapsed: 0.194 s
% 1.59/0.62  % (5843)------------------------------
% 1.59/0.62  % (5843)------------------------------
% 1.59/0.63  % (5849)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.59/0.63  % (5868)Refutation found. Thanks to Tanya!
% 1.59/0.63  % SZS status Theorem for theBenchmark
% 1.59/0.63  % SZS output start Proof for theBenchmark
% 1.59/0.63  fof(f577,plain,(
% 1.59/0.63    $false),
% 1.59/0.63    inference(avatar_sat_refutation,[],[f146,f526,f550,f576])).
% 1.59/0.63  fof(f576,plain,(
% 1.59/0.63    ~spl13_1),
% 1.59/0.63    inference(avatar_contradiction_clause,[],[f575])).
% 1.59/0.63  fof(f575,plain,(
% 1.59/0.63    $false | ~spl13_1),
% 1.59/0.63    inference(subsumption_resolution,[],[f574,f247])).
% 1.59/0.63  fof(f247,plain,(
% 1.59/0.63    ( ! [X15,X16] : (r2_hidden(X16,k1_enumset1(X15,X15,X16))) )),
% 1.59/0.63    inference(trivial_inequality_removal,[],[f246])).
% 1.59/0.63  fof(f246,plain,(
% 1.59/0.63    ( ! [X15,X16] : (k1_xboole_0 != k1_xboole_0 | r2_hidden(X16,k1_enumset1(X15,X15,X16))) )),
% 1.59/0.63    inference(superposition,[],[f120,f233])).
% 1.59/0.63  fof(f233,plain,(
% 1.59/0.63    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.59/0.63    inference(duplicate_literal_removal,[],[f226])).
% 1.59/0.63  fof(f226,plain,(
% 1.59/0.63    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0) | k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.59/0.63    inference(resolution,[],[f216,f215])).
% 1.59/0.63  fof(f215,plain,(
% 1.59/0.63    ( ! [X0,X1] : (~r2_hidden(sK10(k4_xboole_0(X0,X1)),X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.59/0.63    inference(resolution,[],[f179,f87])).
% 1.59/0.63  fof(f87,plain,(
% 1.59/0.63    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 1.59/0.63    inference(cnf_transformation,[],[f47])).
% 1.59/0.63  fof(f47,plain,(
% 1.59/0.63    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((~r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP1(X0,X1,X2)))),
% 1.59/0.63    inference(rectify,[],[f46])).
% 1.59/0.63  fof(f46,plain,(
% 1.59/0.63    ! [X1,X3,X0] : ((sP1(X1,X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP1(X1,X3,X0)))),
% 1.59/0.63    inference(flattening,[],[f45])).
% 1.59/0.63  fof(f45,plain,(
% 1.59/0.63    ! [X1,X3,X0] : ((sP1(X1,X3,X0) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP1(X1,X3,X0)))),
% 1.59/0.63    inference(nnf_transformation,[],[f26])).
% 1.59/0.63  fof(f26,plain,(
% 1.59/0.63    ! [X1,X3,X0] : (sP1(X1,X3,X0) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 1.59/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.59/0.63  fof(f179,plain,(
% 1.59/0.63    ( ! [X0,X1] : (sP1(X0,sK10(k4_xboole_0(X1,X0)),X1) | k1_xboole_0 = k4_xboole_0(X1,X0)) )),
% 1.59/0.63    inference(resolution,[],[f170,f75])).
% 1.59/0.63  fof(f75,plain,(
% 1.59/0.63    ( ! [X0] : (r2_hidden(sK10(X0),X0) | k1_xboole_0 = X0) )),
% 1.59/0.63    inference(cnf_transformation,[],[f40])).
% 1.59/0.63  fof(f40,plain,(
% 1.59/0.63    ! [X0] : ((sP0(sK10(X0),X0) & r2_hidden(sK10(X0),X0)) | k1_xboole_0 = X0)),
% 1.59/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f25,f39])).
% 1.59/0.63  % (5851)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.59/0.63  fof(f39,plain,(
% 1.59/0.63    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) => (sP0(sK10(X0),X0) & r2_hidden(sK10(X0),X0)))),
% 1.59/0.63    introduced(choice_axiom,[])).
% 1.59/0.63  fof(f25,plain,(
% 1.59/0.63    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.59/0.63    inference(definition_folding,[],[f20,f24])).
% 1.59/0.63  fof(f24,plain,(
% 1.59/0.63    ! [X1,X0] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP0(X1,X0))),
% 1.59/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.59/0.63  fof(f20,plain,(
% 1.59/0.63    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.59/0.63    inference(ennf_transformation,[],[f12])).
% 1.59/0.63  fof(f12,axiom,(
% 1.59/0.63    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.59/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 1.59/0.63  fof(f170,plain,(
% 1.59/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | sP1(X2,X0,X1)) )),
% 1.59/0.63    inference(resolution,[],[f82,f128])).
% 1.59/0.63  fof(f128,plain,(
% 1.59/0.63    ( ! [X0,X1] : (sP2(X0,X1,k4_xboole_0(X0,X1))) )),
% 1.59/0.63    inference(equality_resolution,[],[f89])).
% 1.59/0.63  fof(f89,plain,(
% 1.59/0.63    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.59/0.63    inference(cnf_transformation,[],[f48])).
% 1.59/0.63  fof(f48,plain,(
% 1.59/0.63    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP2(X0,X1,X2)) & (sP2(X0,X1,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.59/0.63    inference(nnf_transformation,[],[f28])).
% 1.59/0.63  fof(f28,plain,(
% 1.59/0.63    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP2(X0,X1,X2))),
% 1.59/0.63    inference(definition_folding,[],[f1,f27,f26])).
% 1.59/0.63  fof(f27,plain,(
% 1.59/0.63    ! [X0,X1,X2] : (sP2(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP1(X1,X3,X0)))),
% 1.59/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.59/0.63  fof(f1,axiom,(
% 1.59/0.63    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.59/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.59/0.63  fof(f82,plain,(
% 1.59/0.63    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | ~r2_hidden(X4,X2) | sP1(X1,X4,X0)) )),
% 1.59/0.63    inference(cnf_transformation,[],[f44])).
% 1.59/0.63  fof(f44,plain,(
% 1.59/0.63    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((~sP1(X1,sK11(X0,X1,X2),X0) | ~r2_hidden(sK11(X0,X1,X2),X2)) & (sP1(X1,sK11(X0,X1,X2),X0) | r2_hidden(sK11(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X1,X4,X0)) & (sP1(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 1.59/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f42,f43])).
% 1.59/0.63  fof(f43,plain,(
% 1.59/0.63    ! [X2,X1,X0] : (? [X3] : ((~sP1(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP1(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP1(X1,sK11(X0,X1,X2),X0) | ~r2_hidden(sK11(X0,X1,X2),X2)) & (sP1(X1,sK11(X0,X1,X2),X0) | r2_hidden(sK11(X0,X1,X2),X2))))),
% 1.59/0.63    introduced(choice_axiom,[])).
% 1.59/0.63  fof(f42,plain,(
% 1.59/0.63    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP1(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X1,X4,X0)) & (sP1(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 1.59/0.63    inference(rectify,[],[f41])).
% 1.59/0.63  fof(f41,plain,(
% 1.59/0.63    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP1(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP1(X1,X3,X0)) & (sP1(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP2(X0,X1,X2)))),
% 1.59/0.63    inference(nnf_transformation,[],[f27])).
% 1.59/0.63  fof(f216,plain,(
% 1.59/0.63    ( ! [X2,X3] : (r2_hidden(sK10(k4_xboole_0(X2,X3)),X2) | k1_xboole_0 = k4_xboole_0(X2,X3)) )),
% 1.59/0.63    inference(resolution,[],[f179,f86])).
% 1.59/0.63  fof(f86,plain,(
% 1.59/0.63    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | r2_hidden(X1,X2)) )),
% 1.59/0.63    inference(cnf_transformation,[],[f47])).
% 1.59/0.63  fof(f120,plain,(
% 1.59/0.63    ( ! [X2,X0,X1] : (k1_xboole_0 != k4_xboole_0(k1_enumset1(X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 1.59/0.63    inference(definition_unfolding,[],[f95,f77])).
% 1.59/0.63  fof(f77,plain,(
% 1.59/0.63    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.59/0.63    inference(cnf_transformation,[],[f6])).
% 1.59/0.63  fof(f6,axiom,(
% 1.59/0.63    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.59/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.59/0.63  fof(f95,plain,(
% 1.59/0.63    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.59/0.63    inference(cnf_transformation,[],[f52])).
% 1.59/0.63  fof(f52,plain,(
% 1.59/0.63    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.59/0.63    inference(flattening,[],[f51])).
% 1.59/0.63  fof(f51,plain,(
% 1.59/0.63    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.59/0.63    inference(nnf_transformation,[],[f8])).
% 1.59/0.63  fof(f8,axiom,(
% 1.59/0.63    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.59/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 1.59/0.63  fof(f574,plain,(
% 1.59/0.63    ~r2_hidden(sK9,k1_enumset1(sK9,sK9,sK9)) | ~spl13_1),
% 1.59/0.63    inference(resolution,[],[f564,f354])).
% 1.59/0.63  fof(f354,plain,(
% 1.59/0.63    ( ! [X6] : (sP0(X6,k1_enumset1(X6,X6,X6))) )),
% 1.59/0.63    inference(subsumption_resolution,[],[f349,f205])).
% 1.59/0.63  fof(f205,plain,(
% 1.59/0.63    ( ! [X0,X1] : (k1_xboole_0 != k1_enumset1(X0,X0,X1)) )),
% 1.59/0.63    inference(subsumption_resolution,[],[f203,f151])).
% 1.59/0.63  fof(f151,plain,(
% 1.59/0.63    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.59/0.63    inference(superposition,[],[f129,f68])).
% 1.59/0.63  fof(f68,plain,(
% 1.59/0.63    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.59/0.63    inference(cnf_transformation,[],[f3])).
% 1.59/0.63  fof(f3,axiom,(
% 1.59/0.63    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.59/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.59/0.63  fof(f129,plain,(
% 1.59/0.63    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 1.59/0.63    inference(equality_resolution,[],[f117])).
% 1.59/0.63  fof(f117,plain,(
% 1.59/0.63    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 1.59/0.63    inference(definition_unfolding,[],[f92,f112])).
% 1.59/0.63  fof(f112,plain,(
% 1.59/0.63    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.59/0.63    inference(definition_unfolding,[],[f70,f77])).
% 1.59/0.63  fof(f70,plain,(
% 1.59/0.63    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.59/0.63    inference(cnf_transformation,[],[f5])).
% 1.59/0.63  fof(f5,axiom,(
% 1.59/0.63    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.59/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.59/0.63  fof(f92,plain,(
% 1.59/0.63    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.59/0.63    inference(cnf_transformation,[],[f50])).
% 1.59/0.63  fof(f50,plain,(
% 1.59/0.63    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.59/0.63    inference(flattening,[],[f49])).
% 1.59/0.63  fof(f49,plain,(
% 1.59/0.63    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.59/0.63    inference(nnf_transformation,[],[f7])).
% 1.59/0.63  fof(f7,axiom,(
% 1.59/0.63    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.59/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.59/0.63  fof(f203,plain,(
% 1.59/0.63    ( ! [X0,X1] : (k1_xboole_0 != k1_enumset1(X0,X0,X1) | r2_hidden(X1,k1_xboole_0)) )),
% 1.59/0.63    inference(superposition,[],[f120,f69])).
% 1.59/0.63  fof(f69,plain,(
% 1.59/0.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.59/0.63    inference(cnf_transformation,[],[f2])).
% 1.59/0.63  fof(f2,axiom,(
% 1.59/0.63    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.59/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.59/0.63  fof(f349,plain,(
% 1.59/0.63    ( ! [X6] : (sP0(X6,k1_enumset1(X6,X6,X6)) | k1_xboole_0 = k1_enumset1(X6,X6,X6)) )),
% 1.59/0.63    inference(superposition,[],[f76,f344])).
% 1.59/0.63  fof(f344,plain,(
% 1.59/0.63    ( ! [X0] : (sK10(k1_enumset1(X0,X0,X0)) = X0) )),
% 1.59/0.63    inference(subsumption_resolution,[],[f337,f205])).
% 1.59/0.63  fof(f337,plain,(
% 1.59/0.63    ( ! [X0] : (sK10(k1_enumset1(X0,X0,X0)) = X0 | k1_xboole_0 = k1_enumset1(X0,X0,X0)) )),
% 1.59/0.63    inference(resolution,[],[f336,f75])).
% 1.59/0.63  fof(f336,plain,(
% 1.59/0.63    ( ! [X6,X7] : (~r2_hidden(X7,k1_enumset1(X6,X6,X6)) | X6 = X7) )),
% 1.59/0.63    inference(subsumption_resolution,[],[f335,f151])).
% 1.59/0.63  fof(f335,plain,(
% 1.59/0.63    ( ! [X6,X7] : (r2_hidden(X7,k1_xboole_0) | X6 = X7 | ~r2_hidden(X7,k1_enumset1(X6,X6,X6))) )),
% 1.59/0.63    inference(superposition,[],[f116,f233])).
% 1.59/0.63  fof(f116,plain,(
% 1.59/0.63    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 1.59/0.63    inference(definition_unfolding,[],[f93,f112])).
% 1.59/0.63  fof(f93,plain,(
% 1.59/0.63    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 1.59/0.63    inference(cnf_transformation,[],[f50])).
% 1.59/0.63  fof(f76,plain,(
% 1.59/0.63    ( ! [X0] : (sP0(sK10(X0),X0) | k1_xboole_0 = X0) )),
% 1.59/0.63    inference(cnf_transformation,[],[f40])).
% 1.59/0.63  fof(f564,plain,(
% 1.59/0.63    ( ! [X0] : (~sP0(sK9,X0) | ~r2_hidden(sK9,X0)) ) | ~spl13_1),
% 1.59/0.63    inference(superposition,[],[f127,f559])).
% 1.59/0.63  fof(f559,plain,(
% 1.59/0.63    sK9 = k4_tarski(k4_tarski(sK9,k6_mcart_1(sK6,sK7,sK8,sK9)),k7_mcart_1(sK6,sK7,sK8,sK9)) | ~spl13_1),
% 1.59/0.63    inference(subsumption_resolution,[],[f558,f63])).
% 1.59/0.63  fof(f63,plain,(
% 1.59/0.63    k1_xboole_0 != sK6),
% 1.59/0.63    inference(cnf_transformation,[],[f36])).
% 1.59/0.63  fof(f36,plain,(
% 1.59/0.63    ((sK9 = k7_mcart_1(sK6,sK7,sK8,sK9) | sK9 = k6_mcart_1(sK6,sK7,sK8,sK9) | sK9 = k5_mcart_1(sK6,sK7,sK8,sK9)) & m1_subset_1(sK9,k3_zfmisc_1(sK6,sK7,sK8))) & k1_xboole_0 != sK8 & k1_xboole_0 != sK7 & k1_xboole_0 != sK6),
% 1.59/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f18,f35,f34])).
% 1.59/0.63  fof(f34,plain,(
% 1.59/0.63    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK6,sK7,sK8,X3) = X3 | k6_mcart_1(sK6,sK7,sK8,X3) = X3 | k5_mcart_1(sK6,sK7,sK8,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK6,sK7,sK8))) & k1_xboole_0 != sK8 & k1_xboole_0 != sK7 & k1_xboole_0 != sK6)),
% 1.59/0.63    introduced(choice_axiom,[])).
% 1.59/0.63  fof(f35,plain,(
% 1.59/0.63    ? [X3] : ((k7_mcart_1(sK6,sK7,sK8,X3) = X3 | k6_mcart_1(sK6,sK7,sK8,X3) = X3 | k5_mcart_1(sK6,sK7,sK8,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK6,sK7,sK8))) => ((sK9 = k7_mcart_1(sK6,sK7,sK8,sK9) | sK9 = k6_mcart_1(sK6,sK7,sK8,sK9) | sK9 = k5_mcart_1(sK6,sK7,sK8,sK9)) & m1_subset_1(sK9,k3_zfmisc_1(sK6,sK7,sK8)))),
% 1.59/0.63    introduced(choice_axiom,[])).
% 1.59/0.63  fof(f18,plain,(
% 1.59/0.63    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.59/0.63    inference(ennf_transformation,[],[f17])).
% 1.59/0.63  fof(f17,negated_conjecture,(
% 1.59/0.63    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.59/0.63    inference(negated_conjecture,[],[f16])).
% 1.59/0.63  fof(f16,conjecture,(
% 1.59/0.63    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.59/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).
% 1.59/0.63  fof(f558,plain,(
% 1.59/0.63    sK9 = k4_tarski(k4_tarski(sK9,k6_mcart_1(sK6,sK7,sK8,sK9)),k7_mcart_1(sK6,sK7,sK8,sK9)) | k1_xboole_0 = sK6 | ~spl13_1),
% 1.59/0.63    inference(subsumption_resolution,[],[f557,f64])).
% 1.59/0.63  fof(f64,plain,(
% 1.59/0.63    k1_xboole_0 != sK7),
% 1.59/0.63    inference(cnf_transformation,[],[f36])).
% 1.59/0.63  fof(f557,plain,(
% 1.59/0.63    sK9 = k4_tarski(k4_tarski(sK9,k6_mcart_1(sK6,sK7,sK8,sK9)),k7_mcart_1(sK6,sK7,sK8,sK9)) | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | ~spl13_1),
% 1.59/0.63    inference(subsumption_resolution,[],[f556,f65])).
% 1.59/0.63  fof(f65,plain,(
% 1.59/0.63    k1_xboole_0 != sK8),
% 1.59/0.63    inference(cnf_transformation,[],[f36])).
% 1.59/0.63  fof(f556,plain,(
% 1.59/0.63    sK9 = k4_tarski(k4_tarski(sK9,k6_mcart_1(sK6,sK7,sK8,sK9)),k7_mcart_1(sK6,sK7,sK8,sK9)) | k1_xboole_0 = sK8 | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | ~spl13_1),
% 1.59/0.63    inference(subsumption_resolution,[],[f553,f113])).
% 1.59/0.63  fof(f113,plain,(
% 1.59/0.63    m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8))),
% 1.59/0.63    inference(definition_unfolding,[],[f66,f81])).
% 1.59/0.63  fof(f81,plain,(
% 1.59/0.63    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.59/0.63    inference(cnf_transformation,[],[f10])).
% 1.59/0.63  fof(f10,axiom,(
% 1.59/0.63    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.59/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.59/0.63  fof(f66,plain,(
% 1.59/0.63    m1_subset_1(sK9,k3_zfmisc_1(sK6,sK7,sK8))),
% 1.59/0.63    inference(cnf_transformation,[],[f36])).
% 1.59/0.63  fof(f553,plain,(
% 1.59/0.63    sK9 = k4_tarski(k4_tarski(sK9,k6_mcart_1(sK6,sK7,sK8,sK9)),k7_mcart_1(sK6,sK7,sK8,sK9)) | ~m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) | k1_xboole_0 = sK8 | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | ~spl13_1),
% 1.59/0.63    inference(superposition,[],[f122,f137])).
% 1.59/0.63  fof(f137,plain,(
% 1.59/0.63    sK9 = k5_mcart_1(sK6,sK7,sK8,sK9) | ~spl13_1),
% 1.59/0.63    inference(avatar_component_clause,[],[f135])).
% 1.59/0.63  fof(f135,plain,(
% 1.59/0.63    spl13_1 <=> sK9 = k5_mcart_1(sK6,sK7,sK8,sK9)),
% 1.59/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 1.59/0.63  fof(f122,plain,(
% 1.59/0.63    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.59/0.63    inference(definition_unfolding,[],[f97,f80,f81])).
% 1.59/0.63  fof(f80,plain,(
% 1.59/0.63    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.59/0.63    inference(cnf_transformation,[],[f9])).
% 1.59/0.63  fof(f9,axiom,(
% 1.59/0.63    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.59/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.59/0.63  fof(f97,plain,(
% 1.59/0.63    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.59/0.63    inference(cnf_transformation,[],[f21])).
% 1.59/0.63  fof(f21,plain,(
% 1.59/0.63    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.59/0.63    inference(ennf_transformation,[],[f13])).
% 1.59/0.63  fof(f13,axiom,(
% 1.59/0.63    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.59/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).
% 1.59/0.63  fof(f127,plain,(
% 1.59/0.63    ( ! [X4,X2,X3,X1] : (~sP0(k4_tarski(k4_tarski(X2,X3),X4),X1) | ~r2_hidden(X2,X1)) )),
% 1.59/0.63    inference(equality_resolution,[],[f115])).
% 1.59/0.63  fof(f115,plain,(
% 1.59/0.63    ( ! [X4,X2,X0,X3,X1] : (k4_tarski(k4_tarski(X2,X3),X4) != X0 | ~r2_hidden(X2,X1) | ~sP0(X0,X1)) )),
% 1.59/0.63    inference(definition_unfolding,[],[f73,f80])).
% 1.59/0.63  fof(f73,plain,(
% 1.59/0.63    ( ! [X4,X2,X0,X3,X1] : (k3_mcart_1(X2,X3,X4) != X0 | ~r2_hidden(X2,X1) | ~sP0(X0,X1)) )),
% 1.59/0.63    inference(cnf_transformation,[],[f38])).
% 1.59/0.63  fof(f38,plain,(
% 1.59/0.63    ! [X0,X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X0 | (~r2_hidden(X3,X1) & ~r2_hidden(X2,X1))) | ~sP0(X0,X1))),
% 1.59/0.63    inference(rectify,[],[f37])).
% 1.59/0.63  % (5863)Refutation not found, incomplete strategy% (5863)------------------------------
% 1.59/0.63  % (5863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.63  fof(f37,plain,(
% 1.59/0.63    ! [X1,X0] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP0(X1,X0))),
% 1.59/0.63    inference(nnf_transformation,[],[f24])).
% 1.59/0.63  fof(f550,plain,(
% 1.59/0.63    ~spl13_2),
% 1.59/0.63    inference(avatar_contradiction_clause,[],[f549])).
% 1.59/0.63  % (5863)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.63  
% 1.59/0.63  fof(f549,plain,(
% 1.59/0.63    $false | ~spl13_2),
% 1.59/0.63    inference(subsumption_resolution,[],[f548,f247])).
% 1.59/0.63  fof(f548,plain,(
% 1.59/0.63    ~r2_hidden(sK9,k1_enumset1(sK9,sK9,sK9)) | ~spl13_2),
% 1.59/0.63    inference(resolution,[],[f539,f354])).
% 1.59/0.63  % (5863)Memory used [KB]: 11001
% 1.59/0.63  % (5863)Time elapsed: 0.124 s
% 1.59/0.63  fof(f539,plain,(
% 1.59/0.63    ( ! [X1] : (~sP0(sK9,X1) | ~r2_hidden(sK9,X1)) ) | ~spl13_2),
% 1.59/0.63    inference(superposition,[],[f126,f533])).
% 1.59/0.63  % (5863)------------------------------
% 1.59/0.63  % (5863)------------------------------
% 1.59/0.63  fof(f533,plain,(
% 1.59/0.63    sK9 = k4_tarski(k4_tarski(k5_mcart_1(sK6,sK7,sK8,sK9),sK9),k7_mcart_1(sK6,sK7,sK8,sK9)) | ~spl13_2),
% 1.59/0.63    inference(subsumption_resolution,[],[f532,f63])).
% 1.59/0.63  fof(f532,plain,(
% 1.59/0.63    sK9 = k4_tarski(k4_tarski(k5_mcart_1(sK6,sK7,sK8,sK9),sK9),k7_mcart_1(sK6,sK7,sK8,sK9)) | k1_xboole_0 = sK6 | ~spl13_2),
% 1.59/0.63    inference(subsumption_resolution,[],[f531,f64])).
% 1.59/0.63  fof(f531,plain,(
% 1.59/0.63    sK9 = k4_tarski(k4_tarski(k5_mcart_1(sK6,sK7,sK8,sK9),sK9),k7_mcart_1(sK6,sK7,sK8,sK9)) | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | ~spl13_2),
% 1.59/0.63    inference(subsumption_resolution,[],[f530,f65])).
% 1.59/0.63  fof(f530,plain,(
% 1.59/0.63    sK9 = k4_tarski(k4_tarski(k5_mcart_1(sK6,sK7,sK8,sK9),sK9),k7_mcart_1(sK6,sK7,sK8,sK9)) | k1_xboole_0 = sK8 | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | ~spl13_2),
% 1.59/0.63    inference(subsumption_resolution,[],[f528,f113])).
% 1.59/0.63  fof(f528,plain,(
% 1.59/0.63    sK9 = k4_tarski(k4_tarski(k5_mcart_1(sK6,sK7,sK8,sK9),sK9),k7_mcart_1(sK6,sK7,sK8,sK9)) | ~m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) | k1_xboole_0 = sK8 | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | ~spl13_2),
% 1.59/0.63    inference(superposition,[],[f122,f141])).
% 1.59/0.63  fof(f141,plain,(
% 1.59/0.63    sK9 = k6_mcart_1(sK6,sK7,sK8,sK9) | ~spl13_2),
% 1.59/0.63    inference(avatar_component_clause,[],[f139])).
% 1.59/0.63  fof(f139,plain,(
% 1.59/0.63    spl13_2 <=> sK9 = k6_mcart_1(sK6,sK7,sK8,sK9)),
% 1.59/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 1.59/0.63  fof(f126,plain,(
% 1.59/0.63    ( ! [X4,X2,X3,X1] : (~sP0(k4_tarski(k4_tarski(X2,X3),X4),X1) | ~r2_hidden(X3,X1)) )),
% 1.59/0.63    inference(equality_resolution,[],[f114])).
% 1.59/0.63  fof(f114,plain,(
% 1.59/0.63    ( ! [X4,X2,X0,X3,X1] : (k4_tarski(k4_tarski(X2,X3),X4) != X0 | ~r2_hidden(X3,X1) | ~sP0(X0,X1)) )),
% 1.59/0.63    inference(definition_unfolding,[],[f74,f80])).
% 1.59/0.63  fof(f74,plain,(
% 1.59/0.63    ( ! [X4,X2,X0,X3,X1] : (k3_mcart_1(X2,X3,X4) != X0 | ~r2_hidden(X3,X1) | ~sP0(X0,X1)) )),
% 1.59/0.63    inference(cnf_transformation,[],[f38])).
% 1.59/0.63  fof(f526,plain,(
% 1.59/0.63    ~spl13_3),
% 1.59/0.63    inference(avatar_contradiction_clause,[],[f525])).
% 1.59/0.63  fof(f525,plain,(
% 1.59/0.63    $false | ~spl13_3),
% 1.59/0.63    inference(subsumption_resolution,[],[f524,f63])).
% 1.59/0.63  fof(f524,plain,(
% 1.59/0.63    k1_xboole_0 = sK6 | ~spl13_3),
% 1.59/0.63    inference(subsumption_resolution,[],[f523,f64])).
% 1.59/0.63  fof(f523,plain,(
% 1.59/0.63    k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | ~spl13_3),
% 1.59/0.63    inference(subsumption_resolution,[],[f522,f65])).
% 1.59/0.63  fof(f522,plain,(
% 1.59/0.63    k1_xboole_0 = sK8 | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | ~spl13_3),
% 1.59/0.63    inference(subsumption_resolution,[],[f521,f113])).
% 1.59/0.63  fof(f521,plain,(
% 1.59/0.63    ~m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) | k1_xboole_0 = sK8 | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | ~spl13_3),
% 1.59/0.63    inference(subsumption_resolution,[],[f509,f149])).
% 1.59/0.63  fof(f149,plain,(
% 1.59/0.63    ( ! [X2,X1] : (k4_tarski(X1,X2) != X2) )),
% 1.59/0.63    inference(forward_demodulation,[],[f124,f79])).
% 1.59/0.63  fof(f79,plain,(
% 1.59/0.63    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.59/0.63    inference(cnf_transformation,[],[f15])).
% 1.59/0.63  fof(f15,axiom,(
% 1.59/0.63    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.59/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.59/0.63  fof(f124,plain,(
% 1.59/0.63    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 1.59/0.63    inference(equality_resolution,[],[f72])).
% 1.59/0.63  fof(f72,plain,(
% 1.59/0.63    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 1.59/0.63    inference(cnf_transformation,[],[f19])).
% 1.59/0.63  fof(f19,plain,(
% 1.59/0.63    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 1.59/0.63    inference(ennf_transformation,[],[f11])).
% 1.59/0.63  fof(f11,axiom,(
% 1.59/0.63    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.59/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 1.59/0.63  fof(f509,plain,(
% 1.59/0.63    sK9 = k4_tarski(k4_tarski(k5_mcart_1(sK6,sK7,sK8,sK9),k6_mcart_1(sK6,sK7,sK8,sK9)),sK9) | ~m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) | k1_xboole_0 = sK8 | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | ~spl13_3),
% 1.59/0.63    inference(superposition,[],[f122,f145])).
% 1.59/0.63  fof(f145,plain,(
% 1.59/0.63    sK9 = k7_mcart_1(sK6,sK7,sK8,sK9) | ~spl13_3),
% 1.59/0.63    inference(avatar_component_clause,[],[f143])).
% 1.59/0.63  fof(f143,plain,(
% 1.59/0.63    spl13_3 <=> sK9 = k7_mcart_1(sK6,sK7,sK8,sK9)),
% 1.59/0.63    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).
% 1.59/0.63  fof(f146,plain,(
% 1.59/0.63    spl13_1 | spl13_2 | spl13_3),
% 1.59/0.63    inference(avatar_split_clause,[],[f67,f143,f139,f135])).
% 1.59/0.63  fof(f67,plain,(
% 1.59/0.63    sK9 = k7_mcart_1(sK6,sK7,sK8,sK9) | sK9 = k6_mcart_1(sK6,sK7,sK8,sK9) | sK9 = k5_mcart_1(sK6,sK7,sK8,sK9)),
% 1.59/0.63    inference(cnf_transformation,[],[f36])).
% 1.59/0.63  % SZS output end Proof for theBenchmark
% 1.59/0.63  % (5868)------------------------------
% 1.59/0.63  % (5868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.63  % (5868)Termination reason: Refutation
% 1.59/0.63  
% 1.59/0.63  % (5868)Memory used [KB]: 6524
% 1.59/0.63  % (5868)Time elapsed: 0.220 s
% 1.59/0.63  % (5868)------------------------------
% 1.59/0.63  % (5868)------------------------------
% 1.59/0.63  % (5858)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.59/0.63  % (5840)Success in time 0.264 s
%------------------------------------------------------------------------------
