%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:15 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 140 expanded)
%              Number of leaves         :   14 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  244 ( 490 expanded)
%              Number of equality atoms :   89 ( 194 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f95,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f72,f84,f92,f94])).

fof(f94,plain,
    ( spl6_2
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f86,f61])).

fof(f61,plain,
    ( ~ r2_hidden(sK1,sK3)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl6_2
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f86,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl6_4 ),
    inference(resolution,[],[f70,f39])).

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

fof(f70,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl6_4
  <=> r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f92,plain,
    ( spl6_3
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f90,f65])).

fof(f65,plain,
    ( sK2 != sK4
    | spl6_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl6_3
  <=> sK2 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f90,plain,
    ( sK2 = sK4
    | ~ spl6_4 ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,
    ( sK2 = sK4
    | sK2 = sK4
    | ~ spl6_4 ),
    inference(resolution,[],[f78,f85])).

fof(f85,plain,
    ( r2_hidden(sK2,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | ~ spl6_4 ),
    inference(resolution,[],[f70,f40])).

% (22764)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k3_enumset1(X0,X0,X0,X0,X2))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f30,f52])).

fof(f52,plain,(
    ! [X0,X1] : sP0(X1,X0,k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_enumset1(X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f36,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f84,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f82,f60])).

fof(f60,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f82,plain,
    ( ~ r2_hidden(sK1,sK3)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f79,f75])).

fof(f75,plain,(
    ! [X0,X1] : r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(resolution,[],[f52,f51])).

fof(f51,plain,(
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

fof(f79,plain,
    ( ~ r2_hidden(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | ~ r2_hidden(sK1,sK3)
    | spl6_1 ),
    inference(resolution,[],[f41,f57])).

fof(f57,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl6_1
  <=> r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f72,plain,
    ( spl6_4
    | spl6_2 ),
    inference(avatar_split_clause,[],[f47,f59,f68])).

fof(f47,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) ),
    inference(definition_unfolding,[],[f24,f44])).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f29,f38])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f27,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(f24,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k1_tarski(sK4))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( sK2 != sK4
      | ~ r2_hidden(sK1,sK3)
      | ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k1_tarski(sK4))) )
    & ( ( sK2 = sK4
        & r2_hidden(sK1,sK3) )
      | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k1_tarski(sK4))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f13,f14])).

fof(f14,plain,
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

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | ~ r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | ~ r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <~> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      <=> ( X1 = X3
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f71,plain,
    ( spl6_4
    | spl6_3 ),
    inference(avatar_split_clause,[],[f46,f63,f68])).

fof(f46,plain,
    ( sK2 = sK4
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) ),
    inference(definition_unfolding,[],[f25,f44])).

fof(f25,plain,
    ( sK2 = sK4
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k1_tarski(sK4))) ),
    inference(cnf_transformation,[],[f15])).

fof(f66,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f53,f63,f59,f55])).

fof(f53,plain,
    ( sK2 != sK4
    | ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
    inference(inner_rewriting,[],[f45])).

fof(f45,plain,
    ( sK2 != sK4
    | ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) ),
    inference(definition_unfolding,[],[f26,f44])).

fof(f26,plain,
    ( sK2 != sK4
    | ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k1_tarski(sK4))) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:17:44 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.56  % (22748)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.23/0.56  % (22756)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.23/0.56  % (22746)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.57  % (22746)Refutation found. Thanks to Tanya!
% 0.23/0.57  % SZS status Theorem for theBenchmark
% 0.23/0.57  % (22754)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.23/0.57  % SZS output start Proof for theBenchmark
% 0.23/0.57  fof(f95,plain,(
% 0.23/0.57    $false),
% 0.23/0.57    inference(avatar_sat_refutation,[],[f66,f71,f72,f84,f92,f94])).
% 0.23/0.57  fof(f94,plain,(
% 0.23/0.57    spl6_2 | ~spl6_4),
% 0.23/0.57    inference(avatar_contradiction_clause,[],[f93])).
% 0.23/0.57  fof(f93,plain,(
% 0.23/0.57    $false | (spl6_2 | ~spl6_4)),
% 0.23/0.57    inference(subsumption_resolution,[],[f86,f61])).
% 0.23/0.57  fof(f61,plain,(
% 0.23/0.57    ~r2_hidden(sK1,sK3) | spl6_2),
% 0.23/0.57    inference(avatar_component_clause,[],[f59])).
% 0.23/0.57  fof(f59,plain,(
% 0.23/0.57    spl6_2 <=> r2_hidden(sK1,sK3)),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.23/0.57  fof(f86,plain,(
% 0.23/0.57    r2_hidden(sK1,sK3) | ~spl6_4),
% 0.23/0.57    inference(resolution,[],[f70,f39])).
% 0.23/0.57  fof(f39,plain,(
% 0.23/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f23])).
% 0.23/0.57  fof(f23,plain,(
% 0.23/0.57    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.23/0.57    inference(flattening,[],[f22])).
% 0.23/0.57  fof(f22,plain,(
% 0.23/0.57    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.23/0.57    inference(nnf_transformation,[],[f6])).
% 0.23/0.57  fof(f6,axiom,(
% 0.23/0.57    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.23/0.57  fof(f70,plain,(
% 0.23/0.57    r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) | ~spl6_4),
% 0.23/0.57    inference(avatar_component_clause,[],[f68])).
% 0.23/0.57  fof(f68,plain,(
% 0.23/0.57    spl6_4 <=> r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.23/0.57  fof(f92,plain,(
% 0.23/0.57    spl6_3 | ~spl6_4),
% 0.23/0.57    inference(avatar_contradiction_clause,[],[f91])).
% 0.23/0.57  fof(f91,plain,(
% 0.23/0.57    $false | (spl6_3 | ~spl6_4)),
% 0.23/0.57    inference(subsumption_resolution,[],[f90,f65])).
% 0.23/0.57  fof(f65,plain,(
% 0.23/0.57    sK2 != sK4 | spl6_3),
% 0.23/0.57    inference(avatar_component_clause,[],[f63])).
% 0.23/0.57  fof(f63,plain,(
% 0.23/0.57    spl6_3 <=> sK2 = sK4),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.23/0.57  fof(f90,plain,(
% 0.23/0.57    sK2 = sK4 | ~spl6_4),
% 0.23/0.57    inference(duplicate_literal_removal,[],[f89])).
% 0.23/0.57  fof(f89,plain,(
% 0.23/0.57    sK2 = sK4 | sK2 = sK4 | ~spl6_4),
% 0.23/0.57    inference(resolution,[],[f78,f85])).
% 0.23/0.57  fof(f85,plain,(
% 0.23/0.57    r2_hidden(sK2,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) | ~spl6_4),
% 0.23/0.57    inference(resolution,[],[f70,f40])).
% 0.23/0.57  % (22764)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.23/0.57  fof(f40,plain,(
% 0.23/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f23])).
% 0.23/0.57  fof(f78,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X1,k3_enumset1(X0,X0,X0,X0,X2)) | X0 = X1 | X1 = X2) )),
% 0.23/0.57    inference(resolution,[],[f30,f52])).
% 0.23/0.57  fof(f52,plain,(
% 0.23/0.57    ( ! [X0,X1] : (sP0(X1,X0,k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.23/0.57    inference(equality_resolution,[],[f49])).
% 0.23/0.57  fof(f49,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_enumset1(X0,X0,X0,X0,X1) != X2) )),
% 0.23/0.57    inference(definition_unfolding,[],[f36,f42])).
% 0.23/0.57  fof(f42,plain,(
% 0.23/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.23/0.57    inference(definition_unfolding,[],[f28,f38])).
% 0.23/0.57  fof(f38,plain,(
% 0.23/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f3])).
% 0.23/0.57  fof(f3,axiom,(
% 0.23/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.23/0.57  fof(f28,plain,(
% 0.23/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f5])).
% 0.23/0.57  fof(f5,axiom,(
% 0.23/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 0.23/0.57  fof(f36,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 0.23/0.57    inference(cnf_transformation,[],[f21])).
% 0.23/0.57  fof(f21,plain,(
% 0.23/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 0.23/0.57    inference(nnf_transformation,[],[f11])).
% 0.23/0.57  fof(f11,plain,(
% 0.23/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.23/0.57    inference(definition_folding,[],[f1,f10])).
% 0.23/0.57  fof(f10,plain,(
% 0.23/0.57    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.23/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.23/0.57  fof(f1,axiom,(
% 0.23/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.23/0.57  fof(f30,plain,(
% 0.23/0.57    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 0.23/0.57    inference(cnf_transformation,[],[f20])).
% 0.23/0.57  fof(f20,plain,(
% 0.23/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK5(X0,X1,X2) != X0 & sK5(X0,X1,X2) != X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X0 | sK5(X0,X1,X2) = X1 | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.23/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f19])).
% 0.23/0.57  fof(f19,plain,(
% 0.23/0.57    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK5(X0,X1,X2) != X0 & sK5(X0,X1,X2) != X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X0 | sK5(X0,X1,X2) = X1 | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.23/0.57    introduced(choice_axiom,[])).
% 0.23/0.57  fof(f18,plain,(
% 0.23/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.23/0.57    inference(rectify,[],[f17])).
% 0.23/0.57  fof(f17,plain,(
% 0.23/0.57    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.23/0.57    inference(flattening,[],[f16])).
% 0.23/0.57  fof(f16,plain,(
% 0.23/0.57    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.23/0.57    inference(nnf_transformation,[],[f10])).
% 0.23/0.57  fof(f84,plain,(
% 0.23/0.57    spl6_1 | ~spl6_2),
% 0.23/0.57    inference(avatar_contradiction_clause,[],[f83])).
% 0.23/0.57  fof(f83,plain,(
% 0.23/0.57    $false | (spl6_1 | ~spl6_2)),
% 0.23/0.57    inference(subsumption_resolution,[],[f82,f60])).
% 0.23/0.57  fof(f60,plain,(
% 0.23/0.57    r2_hidden(sK1,sK3) | ~spl6_2),
% 0.23/0.57    inference(avatar_component_clause,[],[f59])).
% 0.23/0.57  fof(f82,plain,(
% 0.23/0.57    ~r2_hidden(sK1,sK3) | spl6_1),
% 0.23/0.57    inference(subsumption_resolution,[],[f79,f75])).
% 0.23/0.57  fof(f75,plain,(
% 0.23/0.57    ( ! [X0,X1] : (r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.23/0.57    inference(resolution,[],[f52,f51])).
% 0.23/0.57  fof(f51,plain,(
% 0.23/0.57    ( ! [X4,X2,X0] : (~sP0(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 0.23/0.57    inference(equality_resolution,[],[f31])).
% 0.23/0.57  fof(f31,plain,(
% 0.23/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP0(X0,X1,X2)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f20])).
% 0.23/0.57  fof(f79,plain,(
% 0.23/0.57    ~r2_hidden(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | ~r2_hidden(sK1,sK3) | spl6_1),
% 0.23/0.57    inference(resolution,[],[f41,f57])).
% 0.23/0.57  fof(f57,plain,(
% 0.23/0.57    ~r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) | spl6_1),
% 0.23/0.57    inference(avatar_component_clause,[],[f55])).
% 0.23/0.57  fof(f55,plain,(
% 0.23/0.57    spl6_1 <=> r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.23/0.57  fof(f41,plain,(
% 0.23/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f23])).
% 0.23/0.57  fof(f72,plain,(
% 0.23/0.57    spl6_4 | spl6_2),
% 0.23/0.57    inference(avatar_split_clause,[],[f47,f59,f68])).
% 0.23/0.57  fof(f47,plain,(
% 0.23/0.57    r2_hidden(sK1,sK3) | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))),
% 0.23/0.57    inference(definition_unfolding,[],[f24,f44])).
% 0.23/0.57  fof(f44,plain,(
% 0.23/0.57    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.23/0.57    inference(definition_unfolding,[],[f27,f43])).
% 0.23/0.57  fof(f43,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.23/0.57    inference(definition_unfolding,[],[f29,f38])).
% 0.23/0.57  fof(f29,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f2])).
% 0.23/0.57  fof(f2,axiom,(
% 0.23/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.23/0.57  fof(f27,plain,(
% 0.23/0.57    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f4])).
% 0.23/0.57  fof(f4,axiom,(
% 0.23/0.57    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0)),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).
% 0.23/0.57  fof(f24,plain,(
% 0.23/0.57    r2_hidden(sK1,sK3) | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k1_tarski(sK4)))),
% 0.23/0.57    inference(cnf_transformation,[],[f15])).
% 0.23/0.57  fof(f15,plain,(
% 0.23/0.57    (sK2 != sK4 | ~r2_hidden(sK1,sK3) | ~r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k1_tarski(sK4)))) & ((sK2 = sK4 & r2_hidden(sK1,sK3)) | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k1_tarski(sK4))))),
% 0.23/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f13,f14])).
% 0.23/0.57  fof(f14,plain,(
% 0.23/0.57    ? [X0,X1,X2,X3] : ((X1 != X3 | ~r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) & ((X1 = X3 & r2_hidden(X0,X2)) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))))) => ((sK2 != sK4 | ~r2_hidden(sK1,sK3) | ~r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k1_tarski(sK4)))) & ((sK2 = sK4 & r2_hidden(sK1,sK3)) | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k1_tarski(sK4)))))),
% 0.23/0.57    introduced(choice_axiom,[])).
% 0.23/0.57  fof(f13,plain,(
% 0.23/0.57    ? [X0,X1,X2,X3] : ((X1 != X3 | ~r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) & ((X1 = X3 & r2_hidden(X0,X2)) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 0.23/0.57    inference(flattening,[],[f12])).
% 0.23/0.57  fof(f12,plain,(
% 0.23/0.57    ? [X0,X1,X2,X3] : (((X1 != X3 | ~r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) & ((X1 = X3 & r2_hidden(X0,X2)) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 0.23/0.57    inference(nnf_transformation,[],[f9])).
% 0.23/0.57  fof(f9,plain,(
% 0.23/0.57    ? [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <~> (X1 = X3 & r2_hidden(X0,X2)))),
% 0.23/0.57    inference(ennf_transformation,[],[f8])).
% 0.23/0.57  fof(f8,negated_conjecture,(
% 0.23/0.57    ~! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 0.23/0.57    inference(negated_conjecture,[],[f7])).
% 0.23/0.57  fof(f7,conjecture,(
% 0.23/0.57    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 0.23/0.57  fof(f71,plain,(
% 0.23/0.57    spl6_4 | spl6_3),
% 0.23/0.57    inference(avatar_split_clause,[],[f46,f63,f68])).
% 0.23/0.57  fof(f46,plain,(
% 0.23/0.57    sK2 = sK4 | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))),
% 0.23/0.57    inference(definition_unfolding,[],[f25,f44])).
% 0.23/0.57  fof(f25,plain,(
% 0.23/0.57    sK2 = sK4 | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k1_tarski(sK4)))),
% 0.23/0.57    inference(cnf_transformation,[],[f15])).
% 0.23/0.57  fof(f66,plain,(
% 0.23/0.57    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 0.23/0.57    inference(avatar_split_clause,[],[f53,f63,f59,f55])).
% 0.23/0.57  fof(f53,plain,(
% 0.23/0.57    sK2 != sK4 | ~r2_hidden(sK1,sK3) | ~r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))),
% 0.23/0.57    inference(inner_rewriting,[],[f45])).
% 0.23/0.57  fof(f45,plain,(
% 0.23/0.57    sK2 != sK4 | ~r2_hidden(sK1,sK3) | ~r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))),
% 0.23/0.57    inference(definition_unfolding,[],[f26,f44])).
% 0.23/0.57  fof(f26,plain,(
% 0.23/0.57    sK2 != sK4 | ~r2_hidden(sK1,sK3) | ~r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(sK3,k1_tarski(sK4)))),
% 0.23/0.57    inference(cnf_transformation,[],[f15])).
% 0.23/0.57  % SZS output end Proof for theBenchmark
% 0.23/0.57  % (22746)------------------------------
% 0.23/0.57  % (22746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.57  % (22746)Termination reason: Refutation
% 0.23/0.57  
% 0.23/0.57  % (22746)Memory used [KB]: 10746
% 0.23/0.57  % (22746)Time elapsed: 0.128 s
% 0.23/0.57  % (22746)------------------------------
% 0.23/0.57  % (22746)------------------------------
% 0.23/0.57  % (22739)Success in time 0.199 s
%------------------------------------------------------------------------------
