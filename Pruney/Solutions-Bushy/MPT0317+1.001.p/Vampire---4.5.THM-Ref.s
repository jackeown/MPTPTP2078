%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0317+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 (  96 expanded)
%              Number of leaves         :   10 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  177 ( 368 expanded)
%              Number of equality atoms :   44 (  97 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f86,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f51,f52,f70,f83,f85])).

fof(f85,plain,
    ( spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f79,f48,f43])).

fof(f43,plain,
    ( spl6_3
  <=> sK2 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f48,plain,
    ( spl6_4
  <=> r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k1_tarski(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f79,plain,
    ( sK2 = sK4
    | ~ spl6_4 ),
    inference(resolution,[],[f76,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f22,f32])).

fof(f32,plain,(
    ! [X0] : sP0(X0,k1_tarski(X0)) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f1,f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( ~ sP0(X0,X1)
      | ~ r2_hidden(X3,X1)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f13,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f76,plain,
    ( r2_hidden(sK2,k1_tarski(sK4))
    | ~ spl6_4 ),
    inference(resolution,[],[f50,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f50,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k1_tarski(sK4)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f83,plain,
    ( spl6_2
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f77,f48,f39])).

fof(f39,plain,
    ( spl6_2
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f77,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl6_4 ),
    inference(resolution,[],[f50,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f70,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f68,f40])).

fof(f40,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f68,plain,
    ( ~ r2_hidden(sK1,sK3)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f64,f54])).

fof(f54,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(resolution,[],[f31,f32])).

fof(f31,plain,(
    ! [X3,X1] :
      ( ~ sP0(X3,X1)
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,
    ( ~ r2_hidden(sK2,k1_tarski(sK2))
    | ~ r2_hidden(sK1,sK3)
    | spl6_1 ),
    inference(resolution,[],[f30,f37])).

fof(f37,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k1_tarski(sK2)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl6_1
  <=> r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,
    ( spl6_4
    | spl6_2 ),
    inference(avatar_split_clause,[],[f19,f39,f48])).

fof(f19,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k1_tarski(sK4))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( sK2 != sK4
      | ~ r2_hidden(sK1,sK3)
      | ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k1_tarski(sK4))) )
    & ( ( sK2 = sK4
        & r2_hidden(sK1,sK3) )
      | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k1_tarski(sK4))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | ~ r2_hidden(X0,X2)
          | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) )
        & ( ( X1 = X3
            & r2_hidden(X0,X2) )
          | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) )
   => ( ( sK2 != sK4
        | ~ r2_hidden(sK1,sK3)
        | ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k1_tarski(sK4))) )
      & ( ( sK2 = sK4
          & r2_hidden(sK1,sK3) )
        | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k1_tarski(sK4))) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | ~ r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | ~ r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <~> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      <=> ( X1 = X3
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f51,plain,
    ( spl6_4
    | spl6_3 ),
    inference(avatar_split_clause,[],[f20,f43,f48])).

fof(f20,plain,
    ( sK2 = sK4
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k1_tarski(sK4))) ),
    inference(cnf_transformation,[],[f11])).

fof(f46,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f33,f43,f39,f35])).

fof(f33,plain,
    ( sK2 != sK4
    | ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k1_tarski(sK2))) ),
    inference(inner_rewriting,[],[f21])).

fof(f21,plain,
    ( sK2 != sK4
    | ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k1_tarski(sK4))) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
