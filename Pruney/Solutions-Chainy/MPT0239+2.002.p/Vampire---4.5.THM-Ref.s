%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 192 expanded)
%              Number of leaves         :   12 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :  305 ( 814 expanded)
%              Number of equality atoms :  152 ( 506 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f111,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f77,f78,f84,f88,f102,f110])).

fof(f110,plain,
    ( spl5_3
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f108,f71])).

fof(f71,plain,
    ( sK1 != sK3
    | spl5_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl5_3
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f108,plain,
    ( sK1 = sK3
    | ~ spl5_4 ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,
    ( sK1 = sK3
    | sK1 = sK3
    | sK1 = sK3
    | ~ spl5_4 ),
    inference(resolution,[],[f98,f57])).

fof(f57,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f27,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK4(X0,X1,X2,X3) != X2
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X2
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X0
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f17])).

fof(f17,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK4(X0,X1,X2,X3) != X2
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X2
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X0
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
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
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
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
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f98,plain,
    ( r2_hidden(sK1,k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ spl5_4 ),
    inference(resolution,[],[f76,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f76,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl5_4
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f102,plain,
    ( spl5_2
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f100,f67])).

fof(f67,plain,
    ( sK0 != sK2
    | spl5_2 ),
    inference(avatar_component_clause,[],[f65])).

% (25867)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f65,plain,
    ( spl5_2
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f100,plain,
    ( sK0 = sK2
    | ~ spl5_4 ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,
    ( sK0 = sK2
    | sK0 = sK2
    | sK0 = sK2
    | ~ spl5_4 ),
    inference(resolution,[],[f97,f57])).

fof(f97,plain,
    ( r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ spl5_4 ),
    inference(resolution,[],[f76,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f88,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f87])).

fof(f87,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f86,f63])).

fof(f63,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl5_1
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f86,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f85,f66])).

fof(f66,plain,
    ( sK0 = sK2
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f85,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK1,sK1,sK1,sK1)))
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f76,f70])).

fof(f70,plain,
    ( sK1 = sK3
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f84,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f82,f52])).

fof(f52,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f30,f26])).

fof(f30,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f82,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f81,f52])).

fof(f81,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4 ),
    inference(resolution,[],[f80,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f80,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4 ),
    inference(backward_demodulation,[],[f79,f66])).

fof(f79,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK1,sK1,sK1,sK1)))
    | ~ spl5_3
    | spl5_4 ),
    inference(backward_demodulation,[],[f75,f70])).

fof(f75,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3)))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f78,plain,
    ( spl5_4
    | spl5_2 ),
    inference(avatar_split_clause,[],[f42,f65,f74])).

fof(f42,plain,
    ( sK0 = sK2
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f21,f39,f39])).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f25,f26])).

fof(f25,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f21,plain,
    ( sK0 = sK2
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( sK1 != sK3
      | sK0 != sK2
      | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) )
    & ( ( sK1 = sK3
        & sK0 = sK2 )
      | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2
          | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) )
        & ( ( X1 = X3
            & X0 = X2 )
          | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) )
   => ( ( sK1 != sK3
        | sK0 != sK2
        | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) )
      & ( ( sK1 = sK3
          & sK0 = sK2 )
        | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) )
      & ( ( X1 = X3
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) )
      & ( ( X1 = X3
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <~> ( X1 = X3
        & X0 = X2 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
      <=> ( X1 = X3
          & X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(f77,plain,
    ( spl5_4
    | spl5_3 ),
    inference(avatar_split_clause,[],[f41,f69,f74])).

fof(f41,plain,
    ( sK1 = sK3
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f22,f39,f39])).

fof(f22,plain,
    ( sK1 = sK3
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f13])).

fof(f72,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f59,f69,f65,f61])).

fof(f59,plain,
    ( sK1 != sK3
    | sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(inner_rewriting,[],[f58])).

fof(f58,plain,
    ( sK1 != sK3
    | sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(inner_rewriting,[],[f40])).

fof(f40,plain,
    ( sK1 != sK3
    | sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f23,f39,f39])).

fof(f23,plain,
    ( sK1 != sK3
    | sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:10:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (25880)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.50  % (25894)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.50  % (25875)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (25886)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.51  % (25895)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.51  % (25887)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.51  % (25887)Refutation not found, incomplete strategy% (25887)------------------------------
% 0.20/0.51  % (25887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25875)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (25887)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (25887)Memory used [KB]: 10746
% 0.20/0.52  % (25887)Time elapsed: 0.106 s
% 0.20/0.52  % (25887)------------------------------
% 0.20/0.52  % (25887)------------------------------
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f111,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f72,f77,f78,f84,f88,f102,f110])).
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    spl5_3 | ~spl5_4),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f109])).
% 0.20/0.52  fof(f109,plain,(
% 0.20/0.52    $false | (spl5_3 | ~spl5_4)),
% 0.20/0.52    inference(subsumption_resolution,[],[f108,f71])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    sK1 != sK3 | spl5_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f69])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    spl5_3 <=> sK1 = sK3),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    sK1 = sK3 | ~spl5_4),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f107])).
% 0.20/0.52  fof(f107,plain,(
% 0.20/0.52    sK1 = sK3 | sK1 = sK3 | sK1 = sK3 | ~spl5_4),
% 0.20/0.52    inference(resolution,[],[f98,f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 0.20/0.52    inference(equality_resolution,[],[f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.20/0.52    inference(definition_unfolding,[],[f27,f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.52    inference(rectify,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.52    inference(flattening,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.52    inference(nnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    r2_hidden(sK1,k2_enumset1(sK3,sK3,sK3,sK3)) | ~spl5_4),
% 0.20/0.52    inference(resolution,[],[f76,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.20/0.52    inference(nnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) | ~spl5_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f74])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    spl5_4 <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.52  fof(f102,plain,(
% 0.20/0.52    spl5_2 | ~spl5_4),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f101])).
% 0.20/0.52  fof(f101,plain,(
% 0.20/0.52    $false | (spl5_2 | ~spl5_4)),
% 0.20/0.52    inference(subsumption_resolution,[],[f100,f67])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    sK0 != sK2 | spl5_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f65])).
% 0.20/0.52  % (25867)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    spl5_2 <=> sK0 = sK2),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.52  fof(f100,plain,(
% 0.20/0.52    sK0 = sK2 | ~spl5_4),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f99])).
% 0.20/0.52  fof(f99,plain,(
% 0.20/0.52    sK0 = sK2 | sK0 = sK2 | sK0 = sK2 | ~spl5_4),
% 0.20/0.52    inference(resolution,[],[f97,f57])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK2)) | ~spl5_4),
% 0.20/0.52    inference(resolution,[],[f76,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f87])).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4)),
% 0.20/0.52    inference(subsumption_resolution,[],[f86,f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) | spl5_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f61])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    spl5_1 <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) | (~spl5_2 | ~spl5_3 | ~spl5_4)),
% 0.20/0.52    inference(forward_demodulation,[],[f85,f66])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    sK0 = sK2 | ~spl5_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f65])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK1,sK1,sK1,sK1))) | (~spl5_3 | ~spl5_4)),
% 0.20/0.52    inference(forward_demodulation,[],[f76,f70])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    sK1 = sK3 | ~spl5_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f69])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    ~spl5_2 | ~spl5_3 | spl5_4),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f83])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    $false | (~spl5_2 | ~spl5_3 | spl5_4)),
% 0.20/0.52    inference(subsumption_resolution,[],[f82,f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 0.20/0.52    inference(equality_resolution,[],[f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 0.20/0.52    inference(equality_resolution,[],[f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.20/0.52    inference(definition_unfolding,[],[f30,f26])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | (~spl5_2 | ~spl5_3 | spl5_4)),
% 0.20/0.52    inference(subsumption_resolution,[],[f81,f52])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | (~spl5_2 | ~spl5_3 | spl5_4)),
% 0.20/0.52    inference(resolution,[],[f80,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) | (~spl5_2 | ~spl5_3 | spl5_4)),
% 0.20/0.52    inference(backward_demodulation,[],[f79,f66])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK1,sK1,sK1,sK1))) | (~spl5_3 | spl5_4)),
% 0.20/0.52    inference(backward_demodulation,[],[f75,f70])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) | spl5_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f74])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    spl5_4 | spl5_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f42,f65,f74])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    sK0 = sK2 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3)))),
% 0.20/0.52    inference(definition_unfolding,[],[f21,f39,f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f24,f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f25,f26])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    sK0 = sK2 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    (sK1 != sK3 | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))) & ((sK1 = sK3 & sK0 = sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) & ((X1 = X3 & X0 = X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))))) => ((sK1 != sK3 | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))) & ((sK1 = sK3 & sK0 = sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) & ((X1 = X3 & X0 = X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 0.20/0.52    inference(flattening,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) & ((X1 = X3 & X0 = X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 0.20/0.52    inference(nnf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <~> (X1 = X3 & X0 = X2))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 0.20/0.52    inference(negated_conjecture,[],[f6])).
% 0.20/0.52  fof(f6,conjecture,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    spl5_4 | spl5_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f41,f69,f74])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    sK1 = sK3 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3)))),
% 0.20/0.52    inference(definition_unfolding,[],[f22,f39,f39])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    sK1 = sK3 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f59,f69,f65,f61])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    sK1 != sK3 | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.20/0.52    inference(inner_rewriting,[],[f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    sK1 != sK3 | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.20/0.52    inference(inner_rewriting,[],[f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    sK1 != sK3 | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3)))),
% 0.20/0.52    inference(definition_unfolding,[],[f23,f39,f39])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    sK1 != sK3 | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (25875)------------------------------
% 0.20/0.52  % (25875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25875)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (25875)Memory used [KB]: 10746
% 0.20/0.52  % (25875)Time elapsed: 0.120 s
% 0.20/0.52  % (25875)------------------------------
% 0.20/0.52  % (25875)------------------------------
% 0.20/0.52  % (25866)Success in time 0.165 s
%------------------------------------------------------------------------------
