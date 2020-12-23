%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:12 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 140 expanded)
%              Number of leaves         :   14 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  256 ( 504 expanded)
%              Number of equality atoms :   89 ( 187 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f104,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f70,f71,f82,f86,f94,f103])).

fof(f103,plain,
    ( spl6_2
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f101,f60])).

fof(f60,plain,
    ( sK1 != sK3
    | spl6_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl6_2
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f101,plain,
    ( sK1 = sK3
    | ~ spl6_4 ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,
    ( sK1 = sK3
    | sK1 = sK3
    | ~ spl6_4 ),
    inference(resolution,[],[f76,f92])).

fof(f92,plain,
    ( r2_hidden(sK1,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3))
    | ~ spl6_4 ),
    inference(resolution,[],[f69,f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f69,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl6_4
  <=> r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k4_enumset1(X0,X0,X0,X0,X0,X2))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f30,f51])).

fof(f51,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f36,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f10])).

fof(f10,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | X1 = X4
      | ~ r2_hidden(X4,X2)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( sK5(X0,X1,X2) != X0
              & sK5(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sK5(X0,X1,X2) = X0
            | sK5(X0,X1,X2) = X1
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK5(X0,X1,X2) != X0
            & sK5(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sK5(X0,X1,X2) = X0
          | sK5(X0,X1,X2) = X1
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
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
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f94,plain,
    ( spl6_3
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f91,f64])).

fof(f64,plain,
    ( ~ r2_hidden(sK2,sK4)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl6_3
  <=> r2_hidden(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f91,plain,
    ( r2_hidden(sK2,sK4)
    | ~ spl6_4 ),
    inference(resolution,[],[f69,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f86,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f84,f56])).

fof(f56,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK4))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl6_1
  <=> r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f84,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK4))
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f69,f59])).

fof(f59,plain,
    ( sK1 = sK3
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f82,plain,
    ( spl6_1
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | spl6_1
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f80,f74])).

fof(f74,plain,(
    ! [X0,X1] : r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(resolution,[],[f51,f50])).

fof(f50,plain,(
    ! [X4,X2,X0] :
      ( ~ sP0(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f80,plain,
    ( ~ r2_hidden(sK1,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))
    | spl6_1
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f77,f63])).

fof(f63,plain,
    ( r2_hidden(sK2,sK4)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f77,plain,
    ( ~ r2_hidden(sK2,sK4)
    | ~ r2_hidden(sK1,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))
    | spl6_1 ),
    inference(resolution,[],[f41,f56])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,
    ( spl6_4
    | spl6_2 ),
    inference(avatar_split_clause,[],[f46,f58,f67])).

fof(f46,plain,
    ( sK1 = sK3
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4)) ),
    inference(definition_unfolding,[],[f24,f43])).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_enumset1)).

fof(f27,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(f24,plain,
    ( sK1 = sK3
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ~ r2_hidden(sK2,sK4)
      | sK1 != sK3
      | ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4)) )
    & ( ( r2_hidden(sK2,sK4)
        & sK1 = sK3 )
      | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r2_hidden(X1,X3)
          | X0 != X2
          | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) )
        & ( ( r2_hidden(X1,X3)
            & X0 = X2 )
          | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) )
   => ( ( ~ r2_hidden(sK2,sK4)
        | sK1 != sK3
        | ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4)) )
      & ( ( r2_hidden(sK2,sK4)
          & sK1 = sK3 )
        | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(X1,X3)
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(X1,X3)
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <~> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      <=> ( r2_hidden(X1,X3)
          & X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f70,plain,
    ( spl6_4
    | spl6_3 ),
    inference(avatar_split_clause,[],[f45,f62,f67])).

fof(f45,plain,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4)) ),
    inference(definition_unfolding,[],[f25,f43])).

fof(f25,plain,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4)) ),
    inference(cnf_transformation,[],[f15])).

fof(f65,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f52,f62,f58,f54])).

fof(f52,plain,
    ( ~ r2_hidden(sK2,sK4)
    | sK1 != sK3
    | ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK4)) ),
    inference(inner_rewriting,[],[f44])).

fof(f44,plain,
    ( ~ r2_hidden(sK2,sK4)
    | sK1 != sK3
    | ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4)) ),
    inference(definition_unfolding,[],[f26,f43])).

fof(f26,plain,
    ( ~ r2_hidden(sK2,sK4)
    | sK1 != sK3
    | ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:50:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (7585)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.22/0.52  % (7594)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.22/0.52  % (7580)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.22/0.52  % (7608)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.22/0.52  % (7603)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.22/0.52  % (7608)Refutation not found, incomplete strategy% (7608)------------------------------
% 1.22/0.52  % (7608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.52  % (7608)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.52  
% 1.22/0.52  % (7580)Refutation not found, incomplete strategy% (7580)------------------------------
% 1.22/0.52  % (7580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.52  % (7580)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.52  
% 1.22/0.52  % (7580)Memory used [KB]: 1663
% 1.22/0.52  % (7580)Time elapsed: 0.105 s
% 1.22/0.52  % (7580)------------------------------
% 1.22/0.52  % (7580)------------------------------
% 1.22/0.52  % (7600)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.22/0.53  % (7603)Refutation not found, incomplete strategy% (7603)------------------------------
% 1.22/0.53  % (7603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (7603)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.53  
% 1.22/0.53  % (7603)Memory used [KB]: 10618
% 1.22/0.53  % (7603)Time elapsed: 0.069 s
% 1.22/0.53  % (7603)------------------------------
% 1.22/0.53  % (7603)------------------------------
% 1.22/0.53  % (7588)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.22/0.53  % (7593)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.22/0.53  % (7584)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.22/0.53  % (7607)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.22/0.53  % (7586)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.22/0.53  % (7593)Refutation not found, incomplete strategy% (7593)------------------------------
% 1.22/0.53  % (7593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (7593)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.53  
% 1.22/0.53  % (7593)Memory used [KB]: 1663
% 1.22/0.53  % (7593)Time elapsed: 0.125 s
% 1.22/0.53  % (7593)------------------------------
% 1.22/0.53  % (7593)------------------------------
% 1.22/0.53  % (7583)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.34/0.53  % (7585)Refutation found. Thanks to Tanya!
% 1.34/0.53  % SZS status Theorem for theBenchmark
% 1.34/0.53  % SZS output start Proof for theBenchmark
% 1.34/0.53  fof(f104,plain,(
% 1.34/0.53    $false),
% 1.34/0.53    inference(avatar_sat_refutation,[],[f65,f70,f71,f82,f86,f94,f103])).
% 1.34/0.53  fof(f103,plain,(
% 1.34/0.53    spl6_2 | ~spl6_4),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f102])).
% 1.34/0.53  fof(f102,plain,(
% 1.34/0.53    $false | (spl6_2 | ~spl6_4)),
% 1.34/0.53    inference(subsumption_resolution,[],[f101,f60])).
% 1.34/0.53  fof(f60,plain,(
% 1.34/0.53    sK1 != sK3 | spl6_2),
% 1.34/0.53    inference(avatar_component_clause,[],[f58])).
% 1.34/0.53  fof(f58,plain,(
% 1.34/0.53    spl6_2 <=> sK1 = sK3),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.34/0.53  fof(f101,plain,(
% 1.34/0.53    sK1 = sK3 | ~spl6_4),
% 1.34/0.53    inference(duplicate_literal_removal,[],[f100])).
% 1.34/0.53  fof(f100,plain,(
% 1.34/0.53    sK1 = sK3 | sK1 = sK3 | ~spl6_4),
% 1.34/0.53    inference(resolution,[],[f76,f92])).
% 1.34/0.53  fof(f92,plain,(
% 1.34/0.53    r2_hidden(sK1,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) | ~spl6_4),
% 1.34/0.53    inference(resolution,[],[f69,f39])).
% 1.34/0.53  fof(f39,plain,(
% 1.34/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f23])).
% 1.34/0.53  fof(f23,plain,(
% 1.34/0.53    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.34/0.53    inference(flattening,[],[f22])).
% 1.34/0.53  fof(f22,plain,(
% 1.34/0.53    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.34/0.53    inference(nnf_transformation,[],[f6])).
% 1.34/0.53  fof(f6,axiom,(
% 1.34/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.34/0.53  fof(f69,plain,(
% 1.34/0.53    r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4)) | ~spl6_4),
% 1.34/0.53    inference(avatar_component_clause,[],[f67])).
% 1.34/0.53  fof(f67,plain,(
% 1.34/0.53    spl6_4 <=> r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.34/0.53  fof(f76,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X1,k4_enumset1(X0,X0,X0,X0,X0,X2)) | X0 = X1 | X1 = X2) )),
% 1.34/0.53    inference(resolution,[],[f30,f51])).
% 1.34/0.53  fof(f51,plain,(
% 1.34/0.53    ( ! [X0,X1] : (sP0(X1,X0,k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.34/0.53    inference(equality_resolution,[],[f48])).
% 1.34/0.53  fof(f48,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2) )),
% 1.34/0.53    inference(definition_unfolding,[],[f36,f42])).
% 1.34/0.53  fof(f42,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.34/0.53    inference(definition_unfolding,[],[f28,f38])).
% 1.34/0.53  fof(f38,plain,(
% 1.34/0.53    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f4])).
% 1.34/0.53  fof(f4,axiom,(
% 1.34/0.53    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).
% 1.34/0.53  fof(f28,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f3])).
% 1.34/0.53  fof(f3,axiom,(
% 1.34/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 1.34/0.53  fof(f36,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 1.34/0.53    inference(cnf_transformation,[],[f21])).
% 1.34/0.53  fof(f21,plain,(
% 1.34/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 1.34/0.53    inference(nnf_transformation,[],[f11])).
% 1.34/0.53  fof(f11,plain,(
% 1.34/0.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.34/0.53    inference(definition_folding,[],[f1,f10])).
% 1.34/0.53  fof(f10,plain,(
% 1.34/0.53    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.34/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.34/0.53  fof(f1,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.34/0.53  fof(f30,plain,(
% 1.34/0.53    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 1.34/0.53    inference(cnf_transformation,[],[f20])).
% 1.34/0.53  fof(f20,plain,(
% 1.34/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK5(X0,X1,X2) != X0 & sK5(X0,X1,X2) != X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X0 | sK5(X0,X1,X2) = X1 | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.34/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f19])).
% 1.34/0.53  fof(f19,plain,(
% 1.34/0.53    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK5(X0,X1,X2) != X0 & sK5(X0,X1,X2) != X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X0 | sK5(X0,X1,X2) = X1 | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.53  fof(f18,plain,(
% 1.34/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.34/0.53    inference(rectify,[],[f17])).
% 1.34/0.53  fof(f17,plain,(
% 1.34/0.53    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.34/0.53    inference(flattening,[],[f16])).
% 1.34/0.53  fof(f16,plain,(
% 1.34/0.53    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.34/0.53    inference(nnf_transformation,[],[f10])).
% 1.34/0.53  fof(f94,plain,(
% 1.34/0.53    spl6_3 | ~spl6_4),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f93])).
% 1.34/0.53  fof(f93,plain,(
% 1.34/0.53    $false | (spl6_3 | ~spl6_4)),
% 1.34/0.53    inference(subsumption_resolution,[],[f91,f64])).
% 1.34/0.53  fof(f64,plain,(
% 1.34/0.53    ~r2_hidden(sK2,sK4) | spl6_3),
% 1.34/0.53    inference(avatar_component_clause,[],[f62])).
% 1.34/0.53  fof(f62,plain,(
% 1.34/0.53    spl6_3 <=> r2_hidden(sK2,sK4)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.34/0.53  fof(f91,plain,(
% 1.34/0.53    r2_hidden(sK2,sK4) | ~spl6_4),
% 1.34/0.53    inference(resolution,[],[f69,f40])).
% 1.34/0.53  fof(f40,plain,(
% 1.34/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f23])).
% 1.34/0.53  fof(f86,plain,(
% 1.34/0.53    spl6_1 | ~spl6_2 | ~spl6_4),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f85])).
% 1.34/0.53  fof(f85,plain,(
% 1.34/0.53    $false | (spl6_1 | ~spl6_2 | ~spl6_4)),
% 1.34/0.53    inference(subsumption_resolution,[],[f84,f56])).
% 1.34/0.53  fof(f56,plain,(
% 1.34/0.53    ~r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK4)) | spl6_1),
% 1.34/0.53    inference(avatar_component_clause,[],[f54])).
% 1.34/0.53  fof(f54,plain,(
% 1.34/0.53    spl6_1 <=> r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK4))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.34/0.53  fof(f84,plain,(
% 1.34/0.53    r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK4)) | (~spl6_2 | ~spl6_4)),
% 1.34/0.53    inference(forward_demodulation,[],[f69,f59])).
% 1.34/0.53  fof(f59,plain,(
% 1.34/0.53    sK1 = sK3 | ~spl6_2),
% 1.34/0.53    inference(avatar_component_clause,[],[f58])).
% 1.34/0.53  fof(f82,plain,(
% 1.34/0.53    spl6_1 | ~spl6_3),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f81])).
% 1.34/0.53  fof(f81,plain,(
% 1.34/0.53    $false | (spl6_1 | ~spl6_3)),
% 1.34/0.53    inference(subsumption_resolution,[],[f80,f74])).
% 1.34/0.53  fof(f74,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.34/0.53    inference(resolution,[],[f51,f50])).
% 1.34/0.53  fof(f50,plain,(
% 1.34/0.53    ( ! [X4,X2,X0] : (~sP0(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 1.34/0.53    inference(equality_resolution,[],[f31])).
% 1.34/0.53  fof(f31,plain,(
% 1.34/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP0(X0,X1,X2)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f20])).
% 1.34/0.53  fof(f80,plain,(
% 1.34/0.53    ~r2_hidden(sK1,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) | (spl6_1 | ~spl6_3)),
% 1.34/0.53    inference(subsumption_resolution,[],[f77,f63])).
% 1.34/0.53  fof(f63,plain,(
% 1.34/0.53    r2_hidden(sK2,sK4) | ~spl6_3),
% 1.34/0.53    inference(avatar_component_clause,[],[f62])).
% 1.34/0.53  fof(f77,plain,(
% 1.34/0.53    ~r2_hidden(sK2,sK4) | ~r2_hidden(sK1,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) | spl6_1),
% 1.34/0.53    inference(resolution,[],[f41,f56])).
% 1.34/0.53  fof(f41,plain,(
% 1.34/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f23])).
% 1.34/0.53  fof(f71,plain,(
% 1.34/0.53    spl6_4 | spl6_2),
% 1.34/0.53    inference(avatar_split_clause,[],[f46,f58,f67])).
% 1.34/0.53  fof(f46,plain,(
% 1.34/0.53    sK1 = sK3 | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4))),
% 1.34/0.53    inference(definition_unfolding,[],[f24,f43])).
% 1.34/0.53  fof(f43,plain,(
% 1.34/0.53    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 1.34/0.53    inference(definition_unfolding,[],[f27,f29])).
% 1.34/0.53  fof(f29,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f5])).
% 1.34/0.53  fof(f5,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_enumset1)).
% 1.34/0.53  fof(f27,plain,(
% 1.34/0.53    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f2])).
% 1.34/0.53  fof(f2,axiom,(
% 1.34/0.53    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).
% 1.34/0.53  fof(f24,plain,(
% 1.34/0.53    sK1 = sK3 | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4))),
% 1.34/0.53    inference(cnf_transformation,[],[f15])).
% 1.34/0.53  fof(f15,plain,(
% 1.34/0.53    (~r2_hidden(sK2,sK4) | sK1 != sK3 | ~r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4))) & ((r2_hidden(sK2,sK4) & sK1 = sK3) | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4)))),
% 1.34/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f13,f14])).
% 1.34/0.53  fof(f14,plain,(
% 1.34/0.53    ? [X0,X1,X2,X3] : ((~r2_hidden(X1,X3) | X0 != X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) & ((r2_hidden(X1,X3) & X0 = X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)))) => ((~r2_hidden(sK2,sK4) | sK1 != sK3 | ~r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4))) & ((r2_hidden(sK2,sK4) & sK1 = sK3) | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4))))),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.53  fof(f13,plain,(
% 1.34/0.53    ? [X0,X1,X2,X3] : ((~r2_hidden(X1,X3) | X0 != X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) & ((r2_hidden(X1,X3) & X0 = X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 1.34/0.53    inference(flattening,[],[f12])).
% 1.34/0.53  fof(f12,plain,(
% 1.34/0.53    ? [X0,X1,X2,X3] : (((~r2_hidden(X1,X3) | X0 != X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) & ((r2_hidden(X1,X3) & X0 = X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 1.34/0.53    inference(nnf_transformation,[],[f9])).
% 1.34/0.53  fof(f9,plain,(
% 1.34/0.53    ? [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <~> (r2_hidden(X1,X3) & X0 = X2))),
% 1.34/0.53    inference(ennf_transformation,[],[f8])).
% 1.34/0.53  fof(f8,negated_conjecture,(
% 1.34/0.53    ~! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 1.34/0.53    inference(negated_conjecture,[],[f7])).
% 1.34/0.53  fof(f7,conjecture,(
% 1.34/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).
% 1.34/0.53  fof(f70,plain,(
% 1.34/0.53    spl6_4 | spl6_3),
% 1.34/0.53    inference(avatar_split_clause,[],[f45,f62,f67])).
% 1.34/0.53  fof(f45,plain,(
% 1.34/0.53    r2_hidden(sK2,sK4) | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4))),
% 1.34/0.53    inference(definition_unfolding,[],[f25,f43])).
% 1.34/0.53  fof(f25,plain,(
% 1.34/0.53    r2_hidden(sK2,sK4) | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4))),
% 1.34/0.53    inference(cnf_transformation,[],[f15])).
% 1.34/0.53  fof(f65,plain,(
% 1.34/0.53    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 1.34/0.53    inference(avatar_split_clause,[],[f52,f62,f58,f54])).
% 1.34/0.53  fof(f52,plain,(
% 1.34/0.53    ~r2_hidden(sK2,sK4) | sK1 != sK3 | ~r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK4))),
% 1.34/0.53    inference(inner_rewriting,[],[f44])).
% 1.34/0.53  fof(f44,plain,(
% 1.34/0.53    ~r2_hidden(sK2,sK4) | sK1 != sK3 | ~r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4))),
% 1.34/0.53    inference(definition_unfolding,[],[f26,f43])).
% 1.34/0.53  fof(f26,plain,(
% 1.34/0.53    ~r2_hidden(sK2,sK4) | sK1 != sK3 | ~r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),sK4))),
% 1.34/0.53    inference(cnf_transformation,[],[f15])).
% 1.34/0.53  % SZS output end Proof for theBenchmark
% 1.34/0.53  % (7585)------------------------------
% 1.34/0.53  % (7585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (7585)Termination reason: Refutation
% 1.34/0.53  
% 1.34/0.53  % (7585)Memory used [KB]: 10746
% 1.34/0.53  % (7585)Time elapsed: 0.122 s
% 1.34/0.53  % (7585)------------------------------
% 1.34/0.53  % (7585)------------------------------
% 1.34/0.54  % (7608)Memory used [KB]: 1663
% 1.34/0.54  % (7578)Success in time 0.171 s
%------------------------------------------------------------------------------
