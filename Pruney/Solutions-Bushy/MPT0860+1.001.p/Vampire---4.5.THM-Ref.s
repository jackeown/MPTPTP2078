%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0860+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  77 expanded)
%              Number of leaves         :    9 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  147 ( 270 expanded)
%              Number of equality atoms :   43 (  94 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f48,f59])).

fof(f59,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f58])).

fof(f58,plain,
    ( $false
    | spl7_2 ),
    inference(subsumption_resolution,[],[f57,f49])).

fof(f49,plain,(
    sK5 != k2_mcart_1(sK2) ),
    inference(subsumption_resolution,[],[f22,f46])).

fof(f46,plain,(
    r2_hidden(k1_mcart_1(sK2),sK3) ),
    inference(resolution,[],[f23,f20])).

fof(f20,plain,(
    r2_hidden(sK2,k2_zfmisc_1(sK3,k2_tarski(sK4,sK5))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( ( sK5 != k2_mcart_1(sK2)
        & sK4 != k2_mcart_1(sK2) )
      | ~ r2_hidden(k1_mcart_1(sK2),sK3) )
    & r2_hidden(sK2,k2_zfmisc_1(sK3,k2_tarski(sK4,sK5))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f5,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ( k2_mcart_1(X0) != X3
            & k2_mcart_1(X0) != X2 )
          | ~ r2_hidden(k1_mcart_1(X0),X1) )
        & r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) )
   => ( ( ( sK5 != k2_mcart_1(sK2)
          & sK4 != k2_mcart_1(sK2) )
        | ~ r2_hidden(k1_mcart_1(sK2),sK3) )
      & r2_hidden(sK2,k2_zfmisc_1(sK3,k2_tarski(sK4,sK5))) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) != X3
          & k2_mcart_1(X0) != X2 )
        | ~ r2_hidden(k1_mcart_1(X0),X1) )
      & r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
       => ( ( k2_mcart_1(X0) = X3
            | k2_mcart_1(X0) = X2 )
          & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f22,plain,
    ( sK5 != k2_mcart_1(sK2)
    | ~ r2_hidden(k1_mcart_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,
    ( sK5 = k2_mcart_1(sK2)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f56,f44])).

fof(f44,plain,
    ( sK4 != k2_mcart_1(sK2)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl7_2
  <=> sK4 = k2_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f56,plain,
    ( sK4 = k2_mcart_1(sK2)
    | sK5 = k2_mcart_1(sK2) ),
    inference(resolution,[],[f55,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( X0 != X1
          & X0 != X2 ) )
      & ( X0 = X1
        | X0 = X2
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X3,X1,X0] :
      ( ( sP0(X3,X1,X0)
        | ( X1 != X3
          & X0 != X3 ) )
      & ( X1 = X3
        | X0 = X3
        | ~ sP0(X3,X1,X0) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X3,X1,X0] :
      ( ( sP0(X3,X1,X0)
        | ( X1 != X3
          & X0 != X3 ) )
      & ( X1 = X3
        | X0 = X3
        | ~ sP0(X3,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X3,X1,X0] :
      ( sP0(X3,X1,X0)
    <=> ( X1 = X3
        | X0 = X3 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f55,plain,(
    sP0(k2_mcart_1(sK2),sK5,sK4) ),
    inference(resolution,[],[f54,f50])).

fof(f50,plain,(
    r2_hidden(k2_mcart_1(sK2),k2_tarski(sK4,sK5)) ),
    inference(resolution,[],[f24,f20])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_tarski(X1,X2))
      | sP0(X0,X2,X1) ) ),
    inference(resolution,[],[f25,f36])).

fof(f36,plain,(
    ! [X0,X1] : sP1(X0,X1,k2_tarski(X0,X1)) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f8,f7])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X3,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X4,X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(sK6(X0,X1,X2),X1,X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sP0(sK6(X0,X1,X2),X1,X0)
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X4,X1,X0) )
            & ( sP0(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f13,f14])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X3,X1,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X3,X1,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(sK6(X0,X1,X2),X1,X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sP0(sK6(X0,X1,X2),X1,X0)
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X4,X1,X0) )
            & ( sP0(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X3,X1,X0) )
            & ( sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f48,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f47])).

fof(f47,plain,
    ( $false
    | spl7_1 ),
    inference(subsumption_resolution,[],[f46,f40])).

fof(f40,plain,
    ( ~ r2_hidden(k1_mcart_1(sK2),sK3)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl7_1
  <=> r2_hidden(k1_mcart_1(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f45,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f21,f42,f38])).

fof(f21,plain,
    ( sK4 != k2_mcart_1(sK2)
    | ~ r2_hidden(k1_mcart_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
