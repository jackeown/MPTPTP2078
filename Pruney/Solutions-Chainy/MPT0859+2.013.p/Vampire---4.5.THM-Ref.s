%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 228 expanded)
%              Number of leaves         :   18 (  71 expanded)
%              Depth                    :   12
%              Number of atoms          :  251 ( 723 expanded)
%              Number of equality atoms :   49 ( 165 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (17780)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f210,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f76,f184,f189,f204,f209])).

fof(f209,plain,
    ( spl7_3
    | ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | spl7_3
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f205,f70])).

fof(f70,plain,
    ( sK3 != k1_mcart_1(sK2)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl7_3
  <=> sK3 = k1_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f205,plain,
    ( sK3 = k1_mcart_1(sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f183,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(condensation,[],[f99])).

fof(f99,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | X2 = X4
      | ~ r2_hidden(X2,k2_enumset1(X4,X4,X4,X4)) ) ),
    inference(resolution,[],[f96,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( ~ r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( ~ r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f96,plain,(
    ! [X6,X7,X5] :
      ( sP0(k2_enumset1(X6,X6,X6,X6),X5,X7)
      | ~ r2_hidden(X5,X7)
      | X5 = X6 ) ),
    inference(resolution,[],[f52,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | sP0(X2,X0,X1) ) ),
    inference(resolution,[],[f36,f56])).

fof(f56,plain,(
    ! [X0,X1] : sP1(X0,X1,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f14,f13])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sP0(X1,sK6(X0,X1,X2),X0)
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sP0(X1,sK6(X0,X1,X2),X0)
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X3,X0) )
            & ( sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f50])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

% (17781)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f183,plain,
    ( r2_hidden(sK3,k2_enumset1(k1_mcart_1(sK2),k1_mcart_1(sK2),k1_mcart_1(sK2),k1_mcart_1(sK2)))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl7_8
  <=> r2_hidden(sK3,k2_enumset1(k1_mcart_1(sK2),k1_mcart_1(sK2),k1_mcart_1(sK2),k1_mcart_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f204,plain,
    ( spl7_1
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl7_1
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f200,f61])).

fof(f61,plain,
    ( sK4 != k1_mcart_1(sK2)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl7_1
  <=> sK4 = k1_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f200,plain,
    ( sK4 = k1_mcart_1(sK2)
    | ~ spl7_7 ),
    inference(resolution,[],[f179,f101])).

fof(f179,plain,
    ( r2_hidden(sK4,k2_enumset1(k1_mcart_1(sK2),k1_mcart_1(sK2),k1_mcart_1(sK2),k1_mcart_1(sK2)))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl7_7
  <=> r2_hidden(sK4,k2_enumset1(k1_mcart_1(sK2),k1_mcart_1(sK2),k1_mcart_1(sK2),k1_mcart_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f189,plain,(
    ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f72,f175])).

fof(f175,plain,
    ( ! [X4] : ~ r2_hidden(k1_mcart_1(sK2),X4)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl7_6
  <=> ! [X4] : ~ r2_hidden(k1_mcart_1(sK2),X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f72,plain,(
    r2_hidden(k1_mcart_1(sK2),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(resolution,[],[f34,f51])).

fof(f51,plain,(
    r2_hidden(sK2,k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f28,f49])).

fof(f28,plain,(
    r2_hidden(sK2,k2_zfmisc_1(k2_tarski(sK3,sK4),sK5)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( ~ r2_hidden(k2_mcart_1(sK2),sK5)
      | ( sK4 != k1_mcart_1(sK2)
        & sK3 != k1_mcart_1(sK2) ) )
    & r2_hidden(sK2,k2_zfmisc_1(k2_tarski(sK3,sK4),sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f10,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r2_hidden(k2_mcart_1(X0),X3)
          | ( k1_mcart_1(X0) != X2
            & k1_mcart_1(X0) != X1 ) )
        & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) )
   => ( ( ~ r2_hidden(k2_mcart_1(sK2),sK5)
        | ( sK4 != k1_mcart_1(sK2)
          & sK3 != k1_mcart_1(sK2) ) )
      & r2_hidden(sK2,k2_zfmisc_1(k2_tarski(sK3,sK4),sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(k2_mcart_1(X0),X3)
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
       => ( r2_hidden(k2_mcart_1(X0),X3)
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
     => ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f184,plain,
    ( spl7_6
    | spl7_7
    | spl7_8 ),
    inference(avatar_split_clause,[],[f163,f181,f177,f174])).

fof(f163,plain,(
    ! [X4] :
      ( r2_hidden(sK3,k2_enumset1(k1_mcart_1(sK2),k1_mcart_1(sK2),k1_mcart_1(sK2),k1_mcart_1(sK2)))
      | r2_hidden(sK4,k2_enumset1(k1_mcart_1(sK2),k1_mcart_1(sK2),k1_mcart_1(sK2),k1_mcart_1(sK2)))
      | ~ r2_hidden(k1_mcart_1(sK2),X4) ) ),
    inference(resolution,[],[f155,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f85,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f85,plain,(
    ! [X0,X1] : ~ sP0(k2_enumset1(X0,X0,X0,X0),X0,X1) ),
    inference(resolution,[],[f83,f57])).

fof(f57,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f46,f50])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k4_xboole_0(X2,X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f37,f56])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X1,X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f155,plain,(
    ! [X3] :
      ( ~ r2_hidden(k1_mcart_1(sK2),X3)
      | r2_hidden(sK3,X3)
      | r2_hidden(sK4,X3) ) ),
    inference(resolution,[],[f150,f72])).

fof(f150,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r2_hidden(X2,k2_enumset1(X5,X5,X5,X4))
      | r2_hidden(X4,X3)
      | r2_hidden(X5,X3)
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f108,f41])).

fof(f108,plain,(
    ! [X14,X12,X15,X13] :
      ( sP0(k2_enumset1(X13,X13,X13,X14),X15,X12)
      | ~ r2_hidden(X15,X12)
      | r2_hidden(X14,X12)
      | r2_hidden(X13,X12) ) ),
    inference(superposition,[],[f82,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_enumset1(X0,X0,X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f76,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f73,f63])).

fof(f63,plain,
    ( spl7_2
  <=> r2_hidden(k2_mcart_1(sK2),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f73,plain,(
    r2_hidden(k2_mcart_1(sK2),sK5) ),
    inference(resolution,[],[f35,f51])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f71,plain,
    ( ~ spl7_3
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f29,f63,f68])).

fof(f29,plain,
    ( ~ r2_hidden(k2_mcart_1(sK2),sK5)
    | sK3 != k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f66,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f30,f63,f59])).

fof(f30,plain,
    ( ~ r2_hidden(k2_mcart_1(sK2),sK5)
    | sK4 != k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:21:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (17793)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (17785)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (17801)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (17776)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (17775)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (17785)Refutation not found, incomplete strategy% (17785)------------------------------
% 0.20/0.53  % (17785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (17776)Refutation not found, incomplete strategy% (17776)------------------------------
% 0.20/0.54  % (17776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (17785)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (17785)Memory used [KB]: 10618
% 0.20/0.54  % (17785)Time elapsed: 0.123 s
% 0.20/0.54  % (17785)------------------------------
% 0.20/0.54  % (17785)------------------------------
% 0.20/0.54  % (17778)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (17801)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  % (17780)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  fof(f210,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f66,f71,f76,f184,f189,f204,f209])).
% 0.20/0.54  fof(f209,plain,(
% 0.20/0.54    spl7_3 | ~spl7_8),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f208])).
% 0.20/0.54  fof(f208,plain,(
% 0.20/0.54    $false | (spl7_3 | ~spl7_8)),
% 0.20/0.54    inference(subsumption_resolution,[],[f205,f70])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    sK3 != k1_mcart_1(sK2) | spl7_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f68])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    spl7_3 <=> sK3 = k1_mcart_1(sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.54  fof(f205,plain,(
% 0.20/0.54    sK3 = k1_mcart_1(sK2) | ~spl7_8),
% 0.20/0.54    inference(resolution,[],[f183,f101])).
% 0.20/0.54  fof(f101,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1) )),
% 0.20/0.54    inference(condensation,[],[f99])).
% 0.20/0.54  fof(f99,plain,(
% 0.20/0.54    ( ! [X4,X2,X3] : (~r2_hidden(X2,X3) | X2 = X4 | ~r2_hidden(X2,k2_enumset1(X4,X4,X4,X4))) )),
% 0.20/0.54    inference(resolution,[],[f96,f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((~r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 0.20/0.54    inference(rectify,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 0.20/0.54    inference(flattening,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 0.20/0.54    inference(nnf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,plain,(
% 0.20/0.54    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 0.20/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.54  fof(f96,plain,(
% 0.20/0.54    ( ! [X6,X7,X5] : (sP0(k2_enumset1(X6,X6,X6,X6),X5,X7) | ~r2_hidden(X5,X7) | X5 = X6) )),
% 0.20/0.54    inference(resolution,[],[f52,f82])).
% 0.20/0.54  fof(f82,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | sP0(X2,X0,X1)) )),
% 0.20/0.54    inference(resolution,[],[f36,f56])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    ( ! [X0,X1] : (sP1(X0,X1,k4_xboole_0(X0,X1))) )),
% 0.20/0.54    inference(equality_resolution,[],[f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.54    inference(nnf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 0.20/0.54    inference(definition_folding,[],[f1,f14,f13])).
% 0.20/0.54  fof(f14,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 0.20/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X1,X4,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sP0(X1,sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f19,f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sP0(X1,sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.20/0.54    inference(rectify,[],[f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 0.20/0.54    inference(nnf_transformation,[],[f14])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f47,f50])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f31,f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f32,f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f4])).
% 0.20/0.54  % (17781)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.20/0.54    inference(flattening,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.20/0.54    inference(nnf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.20/0.54  fof(f183,plain,(
% 0.20/0.54    r2_hidden(sK3,k2_enumset1(k1_mcart_1(sK2),k1_mcart_1(sK2),k1_mcart_1(sK2),k1_mcart_1(sK2))) | ~spl7_8),
% 0.20/0.54    inference(avatar_component_clause,[],[f181])).
% 0.20/0.54  fof(f181,plain,(
% 0.20/0.54    spl7_8 <=> r2_hidden(sK3,k2_enumset1(k1_mcart_1(sK2),k1_mcart_1(sK2),k1_mcart_1(sK2),k1_mcart_1(sK2)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.54  fof(f204,plain,(
% 0.20/0.54    spl7_1 | ~spl7_7),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f203])).
% 0.20/0.54  fof(f203,plain,(
% 0.20/0.54    $false | (spl7_1 | ~spl7_7)),
% 0.20/0.54    inference(subsumption_resolution,[],[f200,f61])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    sK4 != k1_mcart_1(sK2) | spl7_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f59])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    spl7_1 <=> sK4 = k1_mcart_1(sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.54  fof(f200,plain,(
% 0.20/0.54    sK4 = k1_mcart_1(sK2) | ~spl7_7),
% 0.20/0.54    inference(resolution,[],[f179,f101])).
% 0.20/0.54  fof(f179,plain,(
% 0.20/0.54    r2_hidden(sK4,k2_enumset1(k1_mcart_1(sK2),k1_mcart_1(sK2),k1_mcart_1(sK2),k1_mcart_1(sK2))) | ~spl7_7),
% 0.20/0.54    inference(avatar_component_clause,[],[f177])).
% 0.20/0.54  fof(f177,plain,(
% 0.20/0.54    spl7_7 <=> r2_hidden(sK4,k2_enumset1(k1_mcart_1(sK2),k1_mcart_1(sK2),k1_mcart_1(sK2),k1_mcart_1(sK2)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.54  fof(f189,plain,(
% 0.20/0.54    ~spl7_6),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f185])).
% 0.20/0.54  fof(f185,plain,(
% 0.20/0.54    $false | ~spl7_6),
% 0.20/0.54    inference(subsumption_resolution,[],[f72,f175])).
% 0.20/0.54  fof(f175,plain,(
% 0.20/0.54    ( ! [X4] : (~r2_hidden(k1_mcart_1(sK2),X4)) ) | ~spl7_6),
% 0.20/0.54    inference(avatar_component_clause,[],[f174])).
% 0.20/0.54  fof(f174,plain,(
% 0.20/0.54    spl7_6 <=> ! [X4] : ~r2_hidden(k1_mcart_1(sK2),X4)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.54  fof(f72,plain,(
% 0.20/0.54    r2_hidden(k1_mcart_1(sK2),k2_enumset1(sK3,sK3,sK3,sK4))),
% 0.20/0.54    inference(resolution,[],[f34,f51])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    r2_hidden(sK2,k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK4),sK5))),
% 0.20/0.54    inference(definition_unfolding,[],[f28,f49])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    r2_hidden(sK2,k2_zfmisc_1(k2_tarski(sK3,sK4),sK5))),
% 0.20/0.54    inference(cnf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    (~r2_hidden(k2_mcart_1(sK2),sK5) | (sK4 != k1_mcart_1(sK2) & sK3 != k1_mcart_1(sK2))) & r2_hidden(sK2,k2_zfmisc_1(k2_tarski(sK3,sK4),sK5))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f10,f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3] : ((~r2_hidden(k2_mcart_1(X0),X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))) => ((~r2_hidden(k2_mcart_1(sK2),sK5) | (sK4 != k1_mcart_1(sK2) & sK3 != k1_mcart_1(sK2))) & r2_hidden(sK2,k2_zfmisc_1(k2_tarski(sK3,sK4),sK5)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f10,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3] : ((~r2_hidden(k2_mcart_1(X0),X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)))),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) => (r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.20/0.54    inference(negated_conjecture,[],[f8])).
% 0.20/0.54  fof(f8,conjecture,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) => (r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.54  fof(f184,plain,(
% 0.20/0.54    spl7_6 | spl7_7 | spl7_8),
% 0.20/0.54    inference(avatar_split_clause,[],[f163,f181,f177,f174])).
% 0.20/0.54  fof(f163,plain,(
% 0.20/0.54    ( ! [X4] : (r2_hidden(sK3,k2_enumset1(k1_mcart_1(sK2),k1_mcart_1(sK2),k1_mcart_1(sK2),k1_mcart_1(sK2))) | r2_hidden(sK4,k2_enumset1(k1_mcart_1(sK2),k1_mcart_1(sK2),k1_mcart_1(sK2),k1_mcart_1(sK2))) | ~r2_hidden(k1_mcart_1(sK2),X4)) )),
% 0.20/0.54    inference(resolution,[],[f155,f88])).
% 0.20/0.54  fof(f88,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.54    inference(resolution,[],[f85,f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f85,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~sP0(k2_enumset1(X0,X0,X0,X0),X0,X1)) )),
% 0.20/0.54    inference(resolution,[],[f83,f57])).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 0.20/0.54    inference(equality_resolution,[],[f53])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 0.20/0.54    inference(definition_unfolding,[],[f46,f50])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f27])).
% 0.20/0.54  fof(f83,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r2_hidden(X1,k4_xboole_0(X2,X0)) | ~sP0(X0,X1,X2)) )),
% 0.20/0.54    inference(resolution,[],[f37,f56])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X1,X4,X0) | r2_hidden(X4,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f155,plain,(
% 0.20/0.54    ( ! [X3] : (~r2_hidden(k1_mcart_1(sK2),X3) | r2_hidden(sK3,X3) | r2_hidden(sK4,X3)) )),
% 0.20/0.54    inference(resolution,[],[f150,f72])).
% 0.20/0.54  fof(f150,plain,(
% 0.20/0.54    ( ! [X4,X2,X5,X3] : (~r2_hidden(X2,k2_enumset1(X5,X5,X5,X4)) | r2_hidden(X4,X3) | r2_hidden(X5,X3) | ~r2_hidden(X2,X3)) )),
% 0.20/0.54    inference(resolution,[],[f108,f41])).
% 0.20/0.54  fof(f108,plain,(
% 0.20/0.54    ( ! [X14,X12,X15,X13] : (sP0(k2_enumset1(X13,X13,X13,X14),X15,X12) | ~r2_hidden(X15,X12) | r2_hidden(X14,X12) | r2_hidden(X13,X12)) )),
% 0.20/0.54    inference(superposition,[],[f82,f55])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_enumset1(X0,X0,X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f48,f49])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2))),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    spl7_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f73,f63])).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    spl7_2 <=> r2_hidden(k2_mcart_1(sK2),sK5)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.54  fof(f73,plain,(
% 0.20/0.54    r2_hidden(k2_mcart_1(sK2),sK5)),
% 0.20/0.54    inference(resolution,[],[f35,f51])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f11])).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    ~spl7_3 | ~spl7_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f29,f63,f68])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ~r2_hidden(k2_mcart_1(sK2),sK5) | sK3 != k1_mcart_1(sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f17])).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    ~spl7_1 | ~spl7_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f30,f63,f59])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ~r2_hidden(k2_mcart_1(sK2),sK5) | sK4 != k1_mcart_1(sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f17])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (17801)------------------------------
% 0.20/0.54  % (17801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (17801)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (17801)Memory used [KB]: 6268
% 0.20/0.54  % (17801)Time elapsed: 0.119 s
% 0.20/0.54  % (17801)------------------------------
% 0.20/0.54  % (17801)------------------------------
% 0.20/0.54  % (17800)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (17782)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (17777)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (17773)Success in time 0.179 s
%------------------------------------------------------------------------------
