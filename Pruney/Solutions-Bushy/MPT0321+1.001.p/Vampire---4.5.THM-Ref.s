%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0321+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:44 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 341 expanded)
%              Number of leaves         :   21 ( 102 expanded)
%              Depth                    :   12
%              Number of atoms          :  338 (1181 expanded)
%              Number of equality atoms :  113 ( 582 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f360,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f78,f83,f91,f96,f133,f204,f241,f242,f252,f287,f330,f356])).

fof(f356,plain,
    ( ~ spl6_3
    | ~ spl6_9
    | ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f355])).

fof(f355,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f354,f37])).

fof(f37,plain,(
    o_0_0_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f25,f27])).

fof(f27,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f25,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( sK1 != sK3
      | sK0 != sK2 )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) )
   => ( ( sK1 != sK3
        | sK0 != sK2 )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f354,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_13 ),
    inference(backward_demodulation,[],[f331,f61])).

fof(f61,plain,
    ( o_0_0_xboole_0 = sK3
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl6_3
  <=> o_0_0_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f331,plain,
    ( sK1 = sK3
    | ~ spl6_9
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f321,f154])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(X0,sK3),sK1)
        | sK3 = X0
        | ~ r2_hidden(sK5(X0,sK3),X0) )
    | ~ spl6_9 ),
    inference(resolution,[],[f90,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | X0 = X1
      | ~ r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK5(X0,X1),X1)
          | ~ r2_hidden(sK5(X0,X1),X0) )
        & ( r2_hidden(sK5(X0,X1),X1)
          | r2_hidden(sK5(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1),X1)
          | ~ r2_hidden(sK5(X0,X1),X0) )
        & ( r2_hidden(sK5(X0,X1),X1)
          | r2_hidden(sK5(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f90,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl6_9
  <=> ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f321,plain,
    ( r2_hidden(sK5(sK1,sK3),sK1)
    | sK1 = sK3
    | ~ spl6_13 ),
    inference(factoring,[],[f262])).

fof(f262,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(X1,sK3),sK1)
        | r2_hidden(sK5(X1,sK3),X1)
        | sK3 = X1 )
    | ~ spl6_13 ),
    inference(resolution,[],[f114,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f114,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,sK3)
        | r2_hidden(X6,sK1) )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl6_13
  <=> ! [X6] :
        ( ~ r2_hidden(X6,sK3)
        | r2_hidden(X6,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f330,plain,
    ( spl6_2
    | ~ spl6_9
    | ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f329])).

fof(f329,plain,
    ( $false
    | spl6_2
    | ~ spl6_9
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f328,f326])).

fof(f326,plain,
    ( r2_hidden(sK5(sK1,sK3),sK1)
    | spl6_2
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f321,f52])).

fof(f52,plain,
    ( sK1 != sK3
    | spl6_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl6_2
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f328,plain,
    ( ~ r2_hidden(sK5(sK1,sK3),sK1)
    | spl6_2
    | ~ spl6_9
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f327,f52])).

fof(f327,plain,
    ( sK1 = sK3
    | ~ r2_hidden(sK5(sK1,sK3),sK1)
    | spl6_2
    | ~ spl6_9
    | ~ spl6_13 ),
    inference(resolution,[],[f326,f154])).

fof(f287,plain,
    ( spl6_1
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | spl6_1
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f285,f283])).

fof(f283,plain,
    ( r2_hidden(sK5(sK0,sK2),sK0)
    | spl6_1
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f277,f48])).

fof(f48,plain,
    ( sK0 != sK2
    | spl6_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl6_1
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f277,plain,
    ( r2_hidden(sK5(sK0,sK2),sK0)
    | sK0 = sK2
    | ~ spl6_10 ),
    inference(factoring,[],[f258])).

fof(f258,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(X1,sK2),sK0)
        | r2_hidden(sK5(X1,sK2),X1)
        | sK2 = X1 )
    | ~ spl6_10 ),
    inference(resolution,[],[f104,f29])).

fof(f104,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,sK2)
        | r2_hidden(X5,sK0) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl6_10
  <=> ! [X5] :
        ( ~ r2_hidden(X5,sK2)
        | r2_hidden(X5,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f285,plain,
    ( ~ r2_hidden(sK5(sK0,sK2),sK0)
    | spl6_1
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f284,f48])).

fof(f284,plain,
    ( sK0 = sK2
    | ~ r2_hidden(sK5(sK0,sK2),sK0)
    | spl6_1
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(resolution,[],[f283,f97])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(X0,sK2),sK0)
        | sK2 = X0
        | ~ r2_hidden(sK5(X0,sK2),X0) )
    | ~ spl6_7 ),
    inference(resolution,[],[f77,f30])).

fof(f77,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl6_7
  <=> ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f252,plain,
    ( spl6_3
    | ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | spl6_3
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f248,f60])).

fof(f60,plain,
    ( o_0_0_xboole_0 != sK3
    | spl6_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f248,plain,
    ( o_0_0_xboole_0 = sK3
    | ~ spl6_11 ),
    inference(resolution,[],[f107,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f14])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f107,plain,
    ( ! [X4] : ~ r2_hidden(X4,sK3)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl6_11
  <=> ! [X4] : ~ r2_hidden(X4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f242,plain,
    ( spl6_10
    | spl6_11 ),
    inference(avatar_split_clause,[],[f162,f106,f103])).

fof(f162,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,sK3)
      | ~ r2_hidden(X5,sK2)
      | r2_hidden(X5,sK0) ) ),
    inference(resolution,[],[f56,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f56,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X5,sK3)
      | ~ r2_hidden(X4,sK2) ) ),
    inference(superposition,[],[f36,f23])).

fof(f23,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f241,plain,(
    ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f239,f37])).

fof(f239,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f236,f38])).

fof(f38,plain,(
    o_0_0_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f24,f27])).

fof(f24,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).

fof(f236,plain,
    ( o_0_0_xboole_0 = sK0
    | o_0_0_xboole_0 = sK1
    | ~ spl6_5 ),
    inference(trivial_inequality_removal,[],[f235])).

fof(f235,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK0
    | o_0_0_xboole_0 = sK1
    | ~ spl6_5 ),
    inference(superposition,[],[f42,f68])).

fof(f68,plain,
    ( o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl6_5
  <=> o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f42,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 != k2_zfmisc_1(X0,X1)
      | o_0_0_xboole_0 = X0
      | o_0_0_xboole_0 = X1 ) ),
    inference(definition_unfolding,[],[f31,f27,f27,f27])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f204,plain,
    ( spl6_12
    | spl6_13 ),
    inference(avatar_split_clause,[],[f163,f113,f110])).

fof(f110,plain,
    ( spl6_12
  <=> ! [X7] : ~ r2_hidden(X7,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f163,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,sK3)
      | ~ r2_hidden(X7,sK2)
      | r2_hidden(X6,sK1) ) ),
    inference(resolution,[],[f56,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f133,plain,
    ( spl6_5
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | spl6_5
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f131,f69])).

fof(f69,plain,
    ( o_0_0_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f131,plain,
    ( o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f122,f44])).

fof(f44,plain,(
    ! [X1] : o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k2_zfmisc_1(X0,X1)
      | o_0_0_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f32,f27,f27])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f122,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(o_0_0_xboole_0,sK3)
    | ~ spl6_12 ),
    inference(backward_demodulation,[],[f23,f117])).

fof(f117,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl6_12 ),
    inference(resolution,[],[f111,f39])).

fof(f111,plain,
    ( ! [X7] : ~ r2_hidden(X7,sK2)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f110])).

fof(f96,plain,(
    ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f95])).

fof(f95,plain,
    ( $false
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f92,f38])).

fof(f92,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl6_8 ),
    inference(resolution,[],[f87,f39])).

fof(f87,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl6_8
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f91,plain,
    ( spl6_8
    | spl6_9 ),
    inference(avatar_split_clause,[],[f84,f89,f86])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK3)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f55,f36])).

fof(f55,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X3,sK3) ) ),
    inference(superposition,[],[f35,f23])).

fof(f83,plain,(
    ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f79,f37])).

fof(f79,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl6_6 ),
    inference(resolution,[],[f74,f39])).

fof(f74,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl6_6
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f78,plain,
    ( spl6_6
    | spl6_7 ),
    inference(avatar_split_clause,[],[f71,f76,f73])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK2)
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f54,f36])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X0,sK2) ) ),
    inference(superposition,[],[f34,f23])).

fof(f53,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f26,f50,f46])).

fof(f26,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f13])).

%------------------------------------------------------------------------------
