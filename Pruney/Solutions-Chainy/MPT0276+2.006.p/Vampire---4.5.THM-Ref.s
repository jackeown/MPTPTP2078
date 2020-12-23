%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:29 EST 2020

% Result     : Theorem 5.34s
% Output     : Refutation 5.34s
% Verified   : 
% Statistics : Number of formulae       :  303 (1046 expanded)
%              Number of leaves         :   71 ( 377 expanded)
%              Depth                    :   14
%              Number of atoms          :  953 (4252 expanded)
%              Number of equality atoms :  308 (1848 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2576,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f117,f122,f127,f152,f171,f246,f397,f484,f497,f562,f599,f609,f621,f634,f644,f645,f651,f657,f707,f788,f793,f862,f864,f865,f880,f885,f886,f894,f895,f902,f905,f959,f1007,f1072,f1094,f2010,f2088,f2089,f2127,f2182,f2183,f2236,f2317,f2322,f2323,f2336,f2356,f2490,f2506,f2573,f2574,f2575])).

fof(f2575,plain,
    ( sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK0 != sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1))
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2574,plain,
    ( sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK0 != sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1))
    | r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2573,plain,
    ( sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | sK0 != sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1))
    | r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2506,plain,
    ( sK1 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | sK1 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2490,plain,
    ( spl6_93
    | spl6_80
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f2481,f596,f2006,f2487])).

fof(f2487,plain,
    ( spl6_93
  <=> sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_93])])).

fof(f2006,plain,
    ( spl6_80
  <=> sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f596,plain,
    ( spl6_34
  <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f2481,plain,
    ( sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl6_34 ),
    inference(resolution,[],[f598,f107])).

fof(f107,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f55,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK5(X0,X1,X2) != X1
              & sK5(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sK5(X0,X1,X2) = X1
            | sK5(X0,X1,X2) = X0
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK5(X0,X1,X2) != X1
            & sK5(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sK5(X0,X1,X2) = X1
          | sK5(X0,X1,X2) = X0
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
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
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
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
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f598,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f596])).

fof(f2356,plain,
    ( ~ spl6_9
    | spl6_42 ),
    inference(avatar_split_clause,[],[f2339,f704,f164])).

fof(f164,plain,
    ( spl6_9
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f704,plain,
    ( spl6_42
  <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f2339,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl6_42 ),
    inference(duplicate_literal_removal,[],[f745])).

fof(f745,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,sK2)
    | spl6_42 ),
    inference(resolution,[],[f706,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f63,f67])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f706,plain,
    ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK2)
    | spl6_42 ),
    inference(avatar_component_clause,[],[f704])).

fof(f2336,plain,
    ( spl6_25
    | ~ spl6_80 ),
    inference(avatar_contradiction_clause,[],[f2335])).

fof(f2335,plain,
    ( $false
    | spl6_25
    | ~ spl6_80 ),
    inference(subsumption_resolution,[],[f2334,f98])).

fof(f98,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f43,f68])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f67])).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
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
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
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
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f2334,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | spl6_25
    | ~ spl6_80 ),
    inference(forward_demodulation,[],[f478,f2008])).

fof(f2008,plain,
    ( sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl6_80 ),
    inference(avatar_component_clause,[],[f2006])).

fof(f478,plain,
    ( ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl6_25 ),
    inference(avatar_component_clause,[],[f477])).

fof(f477,plain,
    ( spl6_25
  <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f2323,plain,
    ( spl6_77
    | spl6_52
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f1610,f517,f877,f1614])).

fof(f1614,plain,
    ( spl6_77
  <=> sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f877,plain,
    ( spl6_52
  <=> sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f517,plain,
    ( spl6_31
  <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f1610,plain,
    ( sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | ~ spl6_31 ),
    inference(resolution,[],[f519,f107])).

fof(f519,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f517])).

fof(f2322,plain,
    ( spl6_10
    | spl6_2
    | ~ spl6_36
    | ~ spl6_85 ),
    inference(avatar_split_clause,[],[f2321,f2084,f618,f114,f168])).

fof(f168,plain,
    ( spl6_10
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f114,plain,
    ( spl6_2
  <=> k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f618,plain,
    ( spl6_36
  <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f2084,plain,
    ( spl6_85
  <=> sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).

fof(f2321,plain,
    ( r2_hidden(sK1,sK2)
    | spl6_2
    | ~ spl6_36
    | ~ spl6_85 ),
    inference(subsumption_resolution,[],[f2320,f98])).

fof(f2320,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(sK1,sK2)
    | spl6_2
    | ~ spl6_36
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f2319,f2086])).

fof(f2086,plain,
    ( sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl6_85 ),
    inference(avatar_component_clause,[],[f2084])).

fof(f2319,plain,
    ( r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl6_2
    | ~ spl6_36
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f2318,f2086])).

fof(f2318,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl6_2
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f1076,f620])).

fof(f620,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f618])).

fof(f1076,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl6_2 ),
    inference(equality_resolution,[],[f263])).

fof(f263,plain,
    ( ! [X1] :
        ( k2_enumset1(sK1,sK1,sK1,sK1) != X1
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),sK2)
        | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),k2_enumset1(sK0,sK0,sK0,sK1))
        | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),X1) )
    | spl6_2 ),
    inference(superposition,[],[f116,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f54,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).

% (13160)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f116,plain,
    ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK1,sK1,sK1,sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f2317,plain,
    ( spl6_9
    | spl6_10
    | spl6_1 ),
    inference(avatar_split_clause,[],[f331,f109,f168,f164])).

fof(f109,plain,
    ( spl6_1
  <=> k2_enumset1(sK0,sK0,sK0,sK1) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f331,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | spl6_1 ),
    inference(trivial_inequality_removal,[],[f319])).

fof(f319,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK1)
    | r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | spl6_1 ),
    inference(superposition,[],[f111,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X0,X0,X0,X1) = k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k3_xboole_0(k2_enumset1(X0,X0,X0,X1),X2))
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f66,f67,f41,f67])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f111,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f2236,plain,
    ( sK0 != sK5(sK0,sK0,k1_xboole_0)
    | sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | sK0 != sK3(sK0,k1_xboole_0)
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | r2_hidden(sK5(sK0,sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2183,plain,
    ( spl6_85
    | spl6_88
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f2171,f618,f2178,f2084])).

fof(f2178,plain,
    ( spl6_88
  <=> sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).

fof(f2171,plain,
    ( sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl6_36 ),
    inference(resolution,[],[f620,f107])).

fof(f2182,plain,
    ( sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | sK0 != sK3(sK0,k1_xboole_0)
    | ~ r2_hidden(sK0,sK2)
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2127,plain,
    ( spl6_86
    | spl6_87
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f2117,f502,f2124,f2120])).

fof(f2120,plain,
    ( spl6_86
  <=> sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_86])])).

fof(f2124,plain,
    ( spl6_87
  <=> sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).

fof(f502,plain,
    ( spl6_29
  <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f2117,plain,
    ( sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl6_29 ),
    inference(resolution,[],[f504,f107])).

fof(f504,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f502])).

fof(f2089,plain,
    ( sK1 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | sK1 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | sK1 != sK3(sK1,k1_xboole_0)
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1))
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2088,plain,
    ( spl6_85
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f2054,f490,f2084])).

fof(f490,plain,
    ( spl6_27
  <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f2054,plain,
    ( sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl6_27 ),
    inference(duplicate_literal_removal,[],[f2049])).

fof(f2049,plain,
    ( sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl6_27 ),
    inference(resolution,[],[f492,f107])).

fof(f492,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f490])).

fof(f2010,plain,
    ( spl6_80
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f2003,f477,f2006])).

fof(f2003,plain,
    ( sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl6_25 ),
    inference(duplicate_literal_removal,[],[f1998])).

fof(f1998,plain,
    ( sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl6_25 ),
    inference(resolution,[],[f479,f107])).

fof(f479,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f477])).

fof(f1094,plain,
    ( ~ spl6_29
    | spl6_30
    | spl6_1 ),
    inference(avatar_split_clause,[],[f1091,f109,f506,f502])).

fof(f506,plain,
    ( spl6_30
  <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f1091,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | spl6_1 ),
    inference(duplicate_literal_removal,[],[f1090])).

fof(f1090,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | spl6_1 ),
    inference(equality_resolution,[],[f264])).

fof(f264,plain,
    ( ! [X2] :
        ( k2_enumset1(sK0,sK0,sK0,sK1) != X2
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X2),sK2)
        | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X2),k2_enumset1(sK0,sK0,sK0,sK1))
        | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X2),X2) )
    | spl6_1 ),
    inference(superposition,[],[f111,f79])).

fof(f1072,plain,
    ( ~ spl6_25
    | ~ spl6_34
    | spl6_26
    | spl6_3 ),
    inference(avatar_split_clause,[],[f1068,f119,f481,f596,f477])).

fof(f481,plain,
    ( spl6_26
  <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f119,plain,
    ( spl6_3
  <=> k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f1068,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2)
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl6_3 ),
    inference(equality_resolution,[],[f262])).

fof(f262,plain,
    ( ! [X0] :
        ( k2_enumset1(sK0,sK0,sK0,sK0) != X0
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),sK2)
        | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),k2_enumset1(sK0,sK0,sK0,sK1))
        | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),X0) )
    | spl6_3 ),
    inference(superposition,[],[f121,f79])).

fof(f121,plain,
    ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f119])).

fof(f1007,plain,
    ( spl6_22
    | spl6_13
    | spl6_21 ),
    inference(avatar_split_clause,[],[f1006,f419,f241,f423])).

fof(f423,plain,
    ( spl6_22
  <=> sK0 = sK5(sK0,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f241,plain,
    ( spl6_13
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f419,plain,
    ( spl6_21
  <=> r2_hidden(sK5(sK0,sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f1006,plain,
    ( sK0 = sK5(sK0,sK0,k1_xboole_0)
    | spl6_13
    | spl6_21 ),
    inference(subsumption_resolution,[],[f1005,f242])).

fof(f242,plain,
    ( ~ r2_hidden(sK0,k1_xboole_0)
    | spl6_13 ),
    inference(avatar_component_clause,[],[f241])).

fof(f1005,plain,
    ( sK0 = sK5(sK0,sK0,k1_xboole_0)
    | r2_hidden(sK0,k1_xboole_0)
    | spl6_21 ),
    inference(resolution,[],[f420,f306])).

fof(f306,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK5(X6,X6,X7),X7)
      | sK5(X6,X6,X7) = X6
      | r2_hidden(X6,X7) ) ),
    inference(duplicate_literal_removal,[],[f289])).

fof(f289,plain,(
    ! [X6,X7] :
      ( r2_hidden(X6,X7)
      | sK5(X6,X6,X7) = X6
      | sK5(X6,X6,X7) = X6
      | r2_hidden(sK5(X6,X6,X7),X7) ) ),
    inference(superposition,[],[f98,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X0,X0,X0,X1) = X2
      | sK5(X0,X1,X2) = X1
      | sK5(X0,X1,X2) = X0
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f58,f67])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK5(X0,X1,X2) = X1
      | sK5(X0,X1,X2) = X0
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f420,plain,
    ( ~ r2_hidden(sK5(sK0,sK0,k1_xboole_0),k1_xboole_0)
    | spl6_21 ),
    inference(avatar_component_clause,[],[f419])).

fof(f959,plain,
    ( spl6_15
    | spl6_14
    | spl6_18 ),
    inference(avatar_split_clause,[],[f958,f374,f277,f281])).

fof(f281,plain,
    ( spl6_15
  <=> sK1 = sK3(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f277,plain,
    ( spl6_14
  <=> r2_hidden(sK3(sK1,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f374,plain,
    ( spl6_18
  <=> r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f958,plain,
    ( sK1 = sK3(sK1,k1_xboole_0)
    | spl6_14
    | spl6_18 ),
    inference(subsumption_resolution,[],[f945,f375])).

fof(f375,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | spl6_18 ),
    inference(avatar_component_clause,[],[f374])).

fof(f945,plain,
    ( sK1 = sK3(sK1,k1_xboole_0)
    | r2_hidden(sK1,k1_xboole_0)
    | spl6_14 ),
    inference(resolution,[],[f278,f183])).

fof(f183,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK3(X3,X4),X4)
      | sK3(X3,X4) = X3
      | r2_hidden(X3,X4) ) ),
    inference(superposition,[],[f98,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = X1
      | sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f44,f68])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f278,plain,
    ( ~ r2_hidden(sK3(sK1,k1_xboole_0),k1_xboole_0)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f277])).

fof(f905,plain,
    ( spl6_31
    | spl6_4
    | spl6_19 ),
    inference(avatar_split_clause,[],[f515,f390,f124,f517])).

fof(f124,plain,
    ( spl6_4
  <=> k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f390,plain,
    ( spl6_19
  <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f515,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1))
    | spl6_4
    | spl6_19 ),
    inference(subsumption_resolution,[],[f514,f391])).

fof(f391,plain,
    ( ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | spl6_19 ),
    inference(avatar_component_clause,[],[f390])).

fof(f514,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1))
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | spl6_4 ),
    inference(equality_resolution,[],[f221])).

fof(f221,plain,
    ( ! [X3] :
        ( k1_xboole_0 != X3
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X3),k2_enumset1(sK0,sK0,sK0,sK1))
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X3),X3) )
    | spl6_4 ),
    inference(superposition,[],[f126,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f52,f41])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f126,plain,
    ( k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f124])).

fof(f902,plain,
    ( spl6_12
    | spl6_6
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f901,f704,f138,f200])).

fof(f200,plain,
    ( spl6_12
  <=> sK0 = sK3(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f138,plain,
    ( spl6_6
  <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f901,plain,
    ( sK0 = sK3(sK0,k1_xboole_0)
    | spl6_6
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f387,f830])).

fof(f830,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | sK0 = X0 )
    | ~ spl6_42 ),
    inference(resolution,[],[f757,f99])).

fof(f99,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f42,f68])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f757,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl6_42 ),
    inference(resolution,[],[f705,f158])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X0)
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f102,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f41])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f102,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f49,f41])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f705,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK2)
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f704])).

fof(f387,plain,
    ( sK0 = sK3(sK0,k1_xboole_0)
    | r2_hidden(sK3(sK0,k1_xboole_0),k1_xboole_0)
    | spl6_6 ),
    inference(equality_resolution,[],[f257])).

fof(f257,plain,
    ( ! [X0] :
        ( k1_xboole_0 != X0
        | sK0 = sK3(sK0,X0)
        | r2_hidden(sK3(sK0,X0),X0) )
    | spl6_6 ),
    inference(superposition,[],[f140,f74])).

fof(f140,plain,
    ( k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f138])).

fof(f895,plain,
    ( sK0 != sK3(sK1,k1_xboole_0)
    | sK0 != sK3(sK0,k1_xboole_0)
    | ~ r2_hidden(sK3(sK1,k1_xboole_0),k1_xboole_0)
    | r2_hidden(sK3(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f894,plain,
    ( sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | sK0 != sK3(sK0,k1_xboole_0)
    | ~ r2_hidden(sK0,sK2)
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f886,plain,
    ( sK0 != sK5(sK0,sK0,k1_xboole_0)
    | sK0 != sK3(sK0,k1_xboole_0)
    | ~ r2_hidden(sK5(sK0,sK0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(sK3(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f885,plain,
    ( spl6_53
    | ~ spl6_14
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f846,f704,f277,f882])).

fof(f882,plain,
    ( spl6_53
  <=> sK0 = sK3(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f846,plain,
    ( sK0 = sK3(sK1,k1_xboole_0)
    | ~ spl6_14
    | ~ spl6_42 ),
    inference(resolution,[],[f830,f279])).

fof(f279,plain,
    ( r2_hidden(sK3(sK1,k1_xboole_0),k1_xboole_0)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f277])).

fof(f880,plain,
    ( spl6_52
    | ~ spl6_19
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f851,f704,f390,f877])).

fof(f851,plain,
    ( sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | ~ spl6_19
    | ~ spl6_42 ),
    inference(resolution,[],[f830,f392])).

fof(f392,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f390])).

fof(f865,plain,
    ( spl6_22
    | ~ spl6_21
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f853,f704,f419,f423])).

fof(f853,plain,
    ( sK0 = sK5(sK0,sK0,k1_xboole_0)
    | ~ spl6_21
    | ~ spl6_42 ),
    inference(resolution,[],[f830,f421])).

fof(f421,plain,
    ( r2_hidden(sK5(sK0,sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f419])).

fof(f864,plain,
    ( ~ spl6_13
    | ~ spl6_9
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f766,f704,f164,f241])).

fof(f766,plain,
    ( ~ r2_hidden(sK0,k1_xboole_0)
    | ~ spl6_9
    | ~ spl6_42 ),
    inference(resolution,[],[f758,f165])).

fof(f165,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f164])).

fof(f758,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK2)
        | ~ r2_hidden(X2,k1_xboole_0) )
    | ~ spl6_42 ),
    inference(resolution,[],[f705,f157])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f101,f77])).

fof(f101,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f50,f41])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f862,plain,
    ( sK0 != sK3(sK0,k1_xboole_0)
    | r2_hidden(sK0,k1_xboole_0)
    | ~ r2_hidden(sK3(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f793,plain,
    ( ~ spl6_18
    | ~ spl6_42
    | spl6_49 ),
    inference(avatar_contradiction_clause,[],[f789])).

fof(f789,plain,
    ( $false
    | ~ spl6_18
    | ~ spl6_42
    | spl6_49 ),
    inference(unit_resulting_resolution,[],[f376,f705,f741,f158])).

fof(f741,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | spl6_49 ),
    inference(avatar_component_clause,[],[f740])).

fof(f740,plain,
    ( spl6_49
  <=> r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f376,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f374])).

fof(f788,plain,
    ( spl6_35
    | ~ spl6_49 ),
    inference(avatar_contradiction_clause,[],[f787])).

fof(f787,plain,
    ( $false
    | spl6_35
    | ~ spl6_49 ),
    inference(subsumption_resolution,[],[f782,f607])).

fof(f607,plain,
    ( sK0 != sK1
    | spl6_35 ),
    inference(avatar_component_clause,[],[f606])).

fof(f606,plain,
    ( spl6_35
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f782,plain,
    ( sK0 = sK1
    | ~ spl6_49 ),
    inference(duplicate_literal_removal,[],[f778])).

fof(f778,plain,
    ( sK0 = sK1
    | sK0 = sK1
    | ~ spl6_49 ),
    inference(resolution,[],[f742,f107])).

fof(f742,plain,
    ( r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f740])).

fof(f707,plain,
    ( ~ spl6_42
    | spl6_5
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f664,f349,f134,f704])).

fof(f134,plain,
    ( spl6_5
  <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f349,plain,
    ( spl6_17
  <=> k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f664,plain,
    ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK2)
    | spl6_5
    | ~ spl6_17 ),
    inference(superposition,[],[f136,f350])).

fof(f350,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f349])).

fof(f136,plain,
    ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f134])).

fof(f657,plain,
    ( spl6_37
    | ~ spl6_32
    | spl6_33 ),
    inference(avatar_split_clause,[],[f624,f559,f555,f626])).

fof(f626,plain,
    ( spl6_37
  <=> sK0 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f555,plain,
    ( spl6_32
  <=> r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f559,plain,
    ( spl6_33
  <=> sK1 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f624,plain,
    ( sK0 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl6_32
    | spl6_33 ),
    inference(subsumption_resolution,[],[f622,f560])).

fof(f560,plain,
    ( sK1 != sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1))
    | spl6_33 ),
    inference(avatar_component_clause,[],[f559])).

fof(f622,plain,
    ( sK0 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1))
    | sK1 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl6_32 ),
    inference(resolution,[],[f557,f107])).

fof(f557,plain,
    ( r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f555])).

fof(f651,plain,
    ( sK0 != sK1
    | r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f645,plain,
    ( sK0 != sK1
    | k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f644,plain,
    ( spl6_16
    | ~ spl6_33 ),
    inference(avatar_contradiction_clause,[],[f643])).

fof(f643,plain,
    ( $false
    | spl6_16
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f642,f104])).

fof(f104,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f57,f67])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f642,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK1))
    | spl6_16
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f640,f346])).

fof(f346,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) != k2_enumset1(sK1,sK1,sK1,sK1)
    | spl6_16 ),
    inference(avatar_component_clause,[],[f344])).

fof(f344,plain,
    ( spl6_16
  <=> k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f640,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl6_33 ),
    inference(trivial_inequality_removal,[],[f639])).

fof(f639,plain,
    ( sK1 != sK1
    | k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl6_33 ),
    inference(superposition,[],[f73,f561])).

fof(f561,plain,
    ( sK1 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f559])).

fof(f73,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) != X0
      | k2_enumset1(X0,X0,X0,X0) = X1
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f45,f68])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK3(X0,X1) != X0
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f634,plain,
    ( spl6_29
    | spl6_1 ),
    inference(avatar_split_clause,[],[f633,f109,f502])).

fof(f633,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | spl6_1 ),
    inference(duplicate_literal_removal,[],[f632])).

fof(f632,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | spl6_1 ),
    inference(equality_resolution,[],[f220])).

fof(f220,plain,
    ( ! [X2] :
        ( k2_enumset1(sK0,sK0,sK0,sK1) != X2
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X2),k2_enumset1(sK0,sK0,sK0,sK1))
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X2),X2) )
    | spl6_1 ),
    inference(superposition,[],[f111,f81])).

fof(f621,plain,
    ( spl6_27
    | spl6_36
    | spl6_2 ),
    inference(avatar_split_clause,[],[f615,f114,f618,f490])).

fof(f615,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl6_2 ),
    inference(equality_resolution,[],[f219])).

fof(f219,plain,
    ( ! [X1] :
        ( k2_enumset1(sK1,sK1,sK1,sK1) != X1
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),k2_enumset1(sK0,sK0,sK0,sK1))
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),X1) )
    | spl6_2 ),
    inference(superposition,[],[f116,f81])).

fof(f609,plain,
    ( spl6_35
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f601,f344,f606])).

fof(f601,plain,
    ( sK0 = sK1
    | ~ spl6_16 ),
    inference(resolution,[],[f570,f106])).

fof(f106,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f56,f67])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f570,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_enumset1(sK0,sK0,sK0,sK1))
        | sK1 = X3 )
    | ~ spl6_16 ),
    inference(superposition,[],[f99,f345])).

fof(f345,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f344])).

fof(f599,plain,
    ( spl6_25
    | spl6_34
    | spl6_3 ),
    inference(avatar_split_clause,[],[f593,f119,f596,f477])).

fof(f593,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1))
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl6_3 ),
    inference(equality_resolution,[],[f218])).

fof(f218,plain,
    ( ! [X0] :
        ( k2_enumset1(sK0,sK0,sK0,sK0) != X0
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),k2_enumset1(sK0,sK0,sK0,sK1))
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),X0) )
    | spl6_3 ),
    inference(superposition,[],[f121,f81])).

fof(f562,plain,
    ( spl6_32
    | spl6_33
    | spl6_16 ),
    inference(avatar_split_clause,[],[f553,f344,f559,f555])).

fof(f553,plain,
    ( sK1 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1))
    | r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | spl6_16 ),
    inference(equality_resolution,[],[f383])).

fof(f383,plain,
    ( ! [X0] :
        ( k2_enumset1(sK0,sK0,sK0,sK1) != X0
        | sK1 = sK3(sK1,X0)
        | r2_hidden(sK3(sK1,X0),X0) )
    | spl6_16 ),
    inference(superposition,[],[f346,f74])).

fof(f497,plain,
    ( spl6_27
    | ~ spl6_28
    | spl6_2 ),
    inference(avatar_split_clause,[],[f487,f114,f494,f490])).

fof(f494,plain,
    ( spl6_28
  <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f487,plain,
    ( ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl6_2 ),
    inference(equality_resolution,[],[f207])).

fof(f207,plain,
    ( ! [X1] :
        ( k2_enumset1(sK1,sK1,sK1,sK1) != X1
        | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),sK2)
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),X1) )
    | spl6_2 ),
    inference(superposition,[],[f116,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f53,f41])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f484,plain,
    ( spl6_25
    | ~ spl6_26
    | spl6_3 ),
    inference(avatar_split_clause,[],[f474,f119,f481,f477])).

fof(f474,plain,
    ( ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2)
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl6_3 ),
    inference(equality_resolution,[],[f206])).

fof(f206,plain,
    ( ! [X0] :
        ( k2_enumset1(sK0,sK0,sK0,sK0) != X0
        | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),sK2)
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),X0) )
    | spl6_3 ),
    inference(superposition,[],[f121,f80])).

fof(f397,plain,
    ( spl6_19
    | ~ spl6_20
    | spl6_4 ),
    inference(avatar_split_clause,[],[f388,f124,f394,f390])).

fof(f394,plain,
    ( spl6_20
  <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f388,plain,
    ( ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2)
    | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | spl6_4 ),
    inference(equality_resolution,[],[f209])).

fof(f209,plain,
    ( ! [X3] :
        ( k1_xboole_0 != X3
        | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X3),sK2)
        | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X3),X3) )
    | spl6_4 ),
    inference(superposition,[],[f126,f80])).

fof(f246,plain,
    ( spl6_13
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f237,f138,f241])).

fof(f237,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl6_6 ),
    inference(superposition,[],[f104,f139])).

fof(f139,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f138])).

fof(f171,plain,
    ( ~ spl6_9
    | ~ spl6_10
    | spl6_5 ),
    inference(avatar_split_clause,[],[f159,f134,f168,f164])).

fof(f159,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | spl6_5 ),
    inference(resolution,[],[f91,f136])).

fof(f152,plain,
    ( ~ spl6_5
    | spl6_4 ),
    inference(avatar_split_clause,[],[f132,f124,f134])).

fof(f132,plain,
    ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | spl6_4 ),
    inference(trivial_inequality_removal,[],[f131])).

fof(f131,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | spl6_4 ),
    inference(superposition,[],[f126,f77])).

fof(f127,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f72,f124])).

fof(f72,plain,(
    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f35,f41,f67])).

fof(f35,plain,(
    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)
    & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)
    & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
        & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
   => ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
      & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)
      & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)
      & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
      & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
          & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
        & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_zfmisc_1)).

fof(f122,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f71,f119])).

fof(f71,plain,(
    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f36,f41,f67,f68])).

fof(f36,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f117,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f70,f114])).

fof(f70,plain,(
    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f37,f41,f67,f68])).

fof(f37,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f112,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f69,f109])).

fof(f69,plain,(
    k2_enumset1(sK0,sK0,sK0,sK1) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f38,f67,f41,f67])).

fof(f38,plain,(
    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n015.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:50:38 EST 2020
% 0.15/0.35  % CPUTime    : 
% 1.55/0.56  % (12937)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.55/0.56  % (12945)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.55/0.56  % (12938)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.55/0.57  % (12938)Refutation not found, incomplete strategy% (12938)------------------------------
% 1.55/0.57  % (12938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (12946)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.55/0.57  % (12938)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (12938)Memory used [KB]: 1663
% 1.55/0.57  % (12938)Time elapsed: 0.121 s
% 1.55/0.57  % (12938)------------------------------
% 1.55/0.57  % (12938)------------------------------
% 1.55/0.58  % (12959)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.55/0.58  % (12953)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.55/0.58  % (12953)Refutation not found, incomplete strategy% (12953)------------------------------
% 1.55/0.58  % (12953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (12953)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.58  
% 1.55/0.58  % (12953)Memory used [KB]: 10618
% 1.55/0.58  % (12953)Time elapsed: 0.142 s
% 1.55/0.58  % (12953)------------------------------
% 1.55/0.58  % (12953)------------------------------
% 1.55/0.59  % (12941)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.55/0.59  % (12939)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.55/0.60  % (12942)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.55/0.60  % (12940)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.55/0.60  % (12954)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.55/0.60  % (12964)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.55/0.60  % (12955)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.55/0.60  % (12955)Refutation not found, incomplete strategy% (12955)------------------------------
% 1.55/0.60  % (12955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.60  % (12955)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.60  
% 1.55/0.60  % (12955)Memory used [KB]: 1663
% 1.55/0.60  % (12955)Time elapsed: 0.172 s
% 1.55/0.60  % (12955)------------------------------
% 1.55/0.60  % (12955)------------------------------
% 1.55/0.60  % (12943)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.55/0.60  % (12956)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.55/0.60  % (12960)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.55/0.60  % (12965)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.55/0.61  % (12961)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.55/0.61  % (12961)Refutation not found, incomplete strategy% (12961)------------------------------
% 1.55/0.61  % (12961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.61  % (12961)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.61  
% 1.55/0.61  % (12961)Memory used [KB]: 10618
% 1.55/0.61  % (12961)Time elapsed: 0.143 s
% 1.55/0.61  % (12961)------------------------------
% 1.55/0.61  % (12961)------------------------------
% 1.55/0.61  % (12949)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.55/0.61  % (12966)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.55/0.61  % (12948)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.55/0.61  % (12944)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.55/0.61  % (12950)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.55/0.61  % (12947)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.55/0.61  % (12963)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.55/0.61  % (12963)Refutation not found, incomplete strategy% (12963)------------------------------
% 1.55/0.61  % (12963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.61  % (12963)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.61  
% 1.55/0.61  % (12963)Memory used [KB]: 6268
% 1.55/0.61  % (12963)Time elapsed: 0.181 s
% 1.55/0.61  % (12963)------------------------------
% 1.55/0.61  % (12963)------------------------------
% 1.55/0.61  % (12951)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.55/0.61  % (12957)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.55/0.61  % (12952)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.55/0.62  % (12954)Refutation not found, incomplete strategy% (12954)------------------------------
% 1.55/0.62  % (12954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.62  % (12954)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.62  
% 1.55/0.62  % (12954)Memory used [KB]: 1791
% 1.55/0.62  % (12954)Time elapsed: 0.194 s
% 1.55/0.62  % (12954)------------------------------
% 1.55/0.62  % (12954)------------------------------
% 1.55/0.62  % (12958)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.55/0.62  % (12964)Refutation not found, incomplete strategy% (12964)------------------------------
% 1.55/0.62  % (12964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.62  % (12964)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.62  
% 1.55/0.62  % (12964)Memory used [KB]: 6140
% 1.55/0.62  % (12964)Time elapsed: 0.191 s
% 1.55/0.62  % (12964)------------------------------
% 1.55/0.62  % (12964)------------------------------
% 1.55/0.62  % (12962)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.55/0.64  % (12951)Refutation not found, incomplete strategy% (12951)------------------------------
% 1.55/0.64  % (12951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.64  % (12951)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.64  
% 1.55/0.64  % (12951)Memory used [KB]: 1663
% 1.55/0.64  % (12951)Time elapsed: 0.186 s
% 1.55/0.64  % (12951)------------------------------
% 1.55/0.64  % (12951)------------------------------
% 2.49/0.71  % (12994)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.49/0.72  % (12999)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.49/0.73  % (12995)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.73/0.74  % (12940)Refutation not found, incomplete strategy% (12940)------------------------------
% 2.73/0.74  % (12940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.73/0.74  % (12940)Termination reason: Refutation not found, incomplete strategy
% 2.73/0.74  
% 2.73/0.74  % (12940)Memory used [KB]: 6140
% 2.73/0.74  % (12940)Time elapsed: 0.308 s
% 2.73/0.74  % (12940)------------------------------
% 2.73/0.74  % (12940)------------------------------
% 2.73/0.75  % (13002)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.73/0.76  % (13010)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.73/0.76  % (13003)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.73/0.76  % (13003)Refutation not found, incomplete strategy% (13003)------------------------------
% 2.73/0.76  % (13003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.73/0.76  % (13003)Termination reason: Refutation not found, incomplete strategy
% 2.73/0.76  
% 2.73/0.76  % (13003)Memory used [KB]: 10746
% 2.73/0.76  % (13003)Time elapsed: 0.110 s
% 2.73/0.76  % (13003)------------------------------
% 2.73/0.76  % (13003)------------------------------
% 2.73/0.77  % (13006)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.73/0.77  % (13015)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 3.47/0.87  % (12939)Time limit reached!
% 3.47/0.87  % (12939)------------------------------
% 3.47/0.87  % (12939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.47/0.89  % (12939)Termination reason: Time limit
% 3.47/0.89  
% 3.47/0.89  % (12939)Memory used [KB]: 6396
% 3.47/0.89  % (12939)Time elapsed: 0.439 s
% 3.47/0.89  % (12939)------------------------------
% 3.47/0.89  % (12939)------------------------------
% 3.47/0.89  % (13068)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 3.47/0.90  % (13072)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 3.47/0.90  % (13072)Refutation not found, incomplete strategy% (13072)------------------------------
% 3.47/0.90  % (13072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.47/0.90  % (13072)Termination reason: Refutation not found, incomplete strategy
% 3.47/0.90  
% 3.47/0.90  % (13072)Memory used [KB]: 10746
% 3.47/0.90  % (13072)Time elapsed: 0.118 s
% 3.47/0.90  % (13072)------------------------------
% 3.47/0.90  % (13072)------------------------------
% 3.47/0.93  % (12966)Time limit reached!
% 3.47/0.93  % (12966)------------------------------
% 3.47/0.93  % (12966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.47/0.93  % (12966)Termination reason: Time limit
% 3.47/0.93  
% 3.47/0.93  % (12966)Memory used [KB]: 3709
% 3.47/0.93  % (12966)Time elapsed: 0.504 s
% 3.47/0.93  % (12966)------------------------------
% 3.47/0.93  % (12966)------------------------------
% 3.47/0.94  % (12943)Time limit reached!
% 3.47/0.94  % (12943)------------------------------
% 3.47/0.94  % (12943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.47/0.94  % (12943)Termination reason: Time limit
% 3.47/0.94  % (12943)Termination phase: Saturation
% 3.47/0.94  
% 3.47/0.94  % (12943)Memory used [KB]: 14711
% 3.47/0.94  % (12943)Time elapsed: 0.500 s
% 3.47/0.94  % (12943)------------------------------
% 3.47/0.94  % (12943)------------------------------
% 4.26/0.99  % (13149)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 4.26/1.00  % (13157)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 5.34/1.05  % (13161)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 5.34/1.06  % (13161)Refutation not found, incomplete strategy% (13161)------------------------------
% 5.34/1.06  % (13161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.34/1.06  % (13161)Termination reason: Refutation not found, incomplete strategy
% 5.34/1.06  
% 5.34/1.06  % (13161)Memory used [KB]: 10746
% 5.34/1.06  % (13161)Time elapsed: 0.069 s
% 5.34/1.06  % (13161)------------------------------
% 5.34/1.06  % (13161)------------------------------
% 5.34/1.06  % (12995)Refutation found. Thanks to Tanya!
% 5.34/1.06  % SZS status Theorem for theBenchmark
% 5.34/1.06  % SZS output start Proof for theBenchmark
% 5.34/1.06  fof(f2576,plain,(
% 5.34/1.06    $false),
% 5.34/1.06    inference(avatar_sat_refutation,[],[f112,f117,f122,f127,f152,f171,f246,f397,f484,f497,f562,f599,f609,f621,f634,f644,f645,f651,f657,f707,f788,f793,f862,f864,f865,f880,f885,f886,f894,f895,f902,f905,f959,f1007,f1072,f1094,f2010,f2088,f2089,f2127,f2182,f2183,f2236,f2317,f2322,f2323,f2336,f2356,f2490,f2506,f2573,f2574,f2575])).
% 5.34/1.06  fof(f2575,plain,(
% 5.34/1.06    sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | sK0 != sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))),
% 5.34/1.06    introduced(theory_tautology_sat_conflict,[])).
% 5.34/1.06  fof(f2574,plain,(
% 5.34/1.06    sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | sK0 != sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK0,sK2) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2)),
% 5.34/1.06    introduced(theory_tautology_sat_conflict,[])).
% 5.34/1.06  fof(f2573,plain,(
% 5.34/1.06    sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | sK0 != sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK0,sK2) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)),
% 5.34/1.06    introduced(theory_tautology_sat_conflict,[])).
% 5.34/1.06  fof(f2506,plain,(
% 5.34/1.06    sK1 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | sK1 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2)),
% 5.34/1.06    introduced(theory_tautology_sat_conflict,[])).
% 5.34/1.06  fof(f2490,plain,(
% 5.34/1.06    spl6_93 | spl6_80 | ~spl6_34),
% 5.34/1.06    inference(avatar_split_clause,[],[f2481,f596,f2006,f2487])).
% 5.34/1.06  fof(f2487,plain,(
% 5.34/1.06    spl6_93 <=> sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 5.34/1.06    introduced(avatar_definition,[new_symbols(naming,[spl6_93])])).
% 5.34/1.06  fof(f2006,plain,(
% 5.34/1.06    spl6_80 <=> sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 5.34/1.06    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).
% 5.34/1.06  fof(f596,plain,(
% 5.34/1.06    spl6_34 <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1))),
% 5.34/1.06    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 5.34/1.06  fof(f2481,plain,(
% 5.34/1.06    sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl6_34),
% 5.34/1.06    inference(resolution,[],[f598,f107])).
% 5.34/1.06  fof(f107,plain,(
% 5.34/1.06    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 5.34/1.06    inference(equality_resolution,[],[f90])).
% 5.34/1.06  fof(f90,plain,(
% 5.34/1.06    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 5.34/1.06    inference(definition_unfolding,[],[f55,f67])).
% 5.34/1.06  fof(f67,plain,(
% 5.34/1.06    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 5.34/1.06    inference(definition_unfolding,[],[f40,f48])).
% 5.34/1.06  fof(f48,plain,(
% 5.34/1.06    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 5.34/1.06    inference(cnf_transformation,[],[f8])).
% 5.34/1.06  fof(f8,axiom,(
% 5.34/1.06    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 5.34/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 5.34/1.06  fof(f40,plain,(
% 5.34/1.06    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 5.34/1.06    inference(cnf_transformation,[],[f7])).
% 5.34/1.06  fof(f7,axiom,(
% 5.34/1.06    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 5.34/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 5.34/1.06  fof(f55,plain,(
% 5.34/1.06    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 5.34/1.06    inference(cnf_transformation,[],[f30])).
% 5.34/1.06  fof(f30,plain,(
% 5.34/1.06    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 5.34/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f29])).
% 5.34/1.06  fof(f29,plain,(
% 5.34/1.06    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2))))),
% 5.34/1.06    introduced(choice_axiom,[])).
% 5.34/1.06  fof(f28,plain,(
% 5.34/1.06    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 5.34/1.06    inference(rectify,[],[f27])).
% 5.34/1.06  fof(f27,plain,(
% 5.34/1.06    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 5.34/1.06    inference(flattening,[],[f26])).
% 5.34/1.06  fof(f26,plain,(
% 5.34/1.06    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 5.34/1.06    inference(nnf_transformation,[],[f5])).
% 5.34/1.06  fof(f5,axiom,(
% 5.34/1.06    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 5.34/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 5.34/1.06  fof(f598,plain,(
% 5.34/1.06    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl6_34),
% 5.34/1.06    inference(avatar_component_clause,[],[f596])).
% 5.34/1.06  fof(f2356,plain,(
% 5.34/1.06    ~spl6_9 | spl6_42),
% 5.34/1.06    inference(avatar_split_clause,[],[f2339,f704,f164])).
% 5.34/1.06  fof(f164,plain,(
% 5.34/1.06    spl6_9 <=> r2_hidden(sK0,sK2)),
% 5.34/1.06    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 5.34/1.06  fof(f704,plain,(
% 5.34/1.06    spl6_42 <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK2)),
% 5.34/1.06    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 5.34/1.06  fof(f2339,plain,(
% 5.34/1.06    ~r2_hidden(sK0,sK2) | spl6_42),
% 5.34/1.06    inference(duplicate_literal_removal,[],[f745])).
% 5.34/1.06  fof(f745,plain,(
% 5.34/1.06    ~r2_hidden(sK0,sK2) | ~r2_hidden(sK0,sK2) | spl6_42),
% 5.34/1.06    inference(resolution,[],[f706,f91])).
% 5.34/1.06  fof(f91,plain,(
% 5.34/1.06    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 5.34/1.06    inference(definition_unfolding,[],[f63,f67])).
% 5.34/1.06  fof(f63,plain,(
% 5.34/1.06    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 5.34/1.06    inference(cnf_transformation,[],[f32])).
% 5.34/1.06  fof(f32,plain,(
% 5.34/1.06    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 5.34/1.06    inference(flattening,[],[f31])).
% 5.34/1.06  fof(f31,plain,(
% 5.34/1.06    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 5.34/1.06    inference(nnf_transformation,[],[f9])).
% 5.34/1.06  fof(f9,axiom,(
% 5.34/1.06    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 5.34/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 5.34/1.06  fof(f706,plain,(
% 5.34/1.06    ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK2) | spl6_42),
% 5.34/1.06    inference(avatar_component_clause,[],[f704])).
% 5.34/1.06  fof(f2336,plain,(
% 5.34/1.06    spl6_25 | ~spl6_80),
% 5.34/1.06    inference(avatar_contradiction_clause,[],[f2335])).
% 5.34/1.06  fof(f2335,plain,(
% 5.34/1.06    $false | (spl6_25 | ~spl6_80)),
% 5.34/1.06    inference(subsumption_resolution,[],[f2334,f98])).
% 5.34/1.06  fof(f98,plain,(
% 5.34/1.06    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 5.34/1.06    inference(equality_resolution,[],[f97])).
% 5.34/1.06  fof(f97,plain,(
% 5.34/1.06    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 5.34/1.06    inference(equality_resolution,[],[f75])).
% 5.34/1.06  fof(f75,plain,(
% 5.34/1.06    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 5.34/1.06    inference(definition_unfolding,[],[f43,f68])).
% 5.34/1.06  fof(f68,plain,(
% 5.34/1.06    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 5.34/1.06    inference(definition_unfolding,[],[f39,f67])).
% 5.34/1.06  fof(f39,plain,(
% 5.34/1.06    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 5.34/1.06    inference(cnf_transformation,[],[f6])).
% 5.34/1.06  fof(f6,axiom,(
% 5.34/1.06    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 5.34/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 5.34/1.06  fof(f43,plain,(
% 5.34/1.06    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 5.34/1.06    inference(cnf_transformation,[],[f19])).
% 5.34/1.06  fof(f19,plain,(
% 5.34/1.06    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 5.34/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 5.34/1.06  fof(f18,plain,(
% 5.34/1.06    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 5.34/1.06    introduced(choice_axiom,[])).
% 5.34/1.06  fof(f17,plain,(
% 5.34/1.06    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 5.34/1.06    inference(rectify,[],[f16])).
% 5.34/1.06  fof(f16,plain,(
% 5.34/1.06    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 5.34/1.06    inference(nnf_transformation,[],[f4])).
% 5.34/1.06  fof(f4,axiom,(
% 5.34/1.06    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 5.34/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 5.34/1.06  fof(f2334,plain,(
% 5.34/1.06    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | (spl6_25 | ~spl6_80)),
% 5.34/1.06    inference(forward_demodulation,[],[f478,f2008])).
% 5.34/1.06  fof(f2008,plain,(
% 5.34/1.06    sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl6_80),
% 5.34/1.06    inference(avatar_component_clause,[],[f2006])).
% 5.34/1.06  fof(f478,plain,(
% 5.34/1.06    ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl6_25),
% 5.34/1.06    inference(avatar_component_clause,[],[f477])).
% 5.34/1.06  fof(f477,plain,(
% 5.34/1.06    spl6_25 <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))),
% 5.34/1.06    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 5.34/1.06  fof(f2323,plain,(
% 5.34/1.06    spl6_77 | spl6_52 | ~spl6_31),
% 5.34/1.06    inference(avatar_split_clause,[],[f1610,f517,f877,f1614])).
% 5.34/1.06  fof(f1614,plain,(
% 5.34/1.06    spl6_77 <=> sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)),
% 5.34/1.06    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).
% 5.34/1.06  fof(f877,plain,(
% 5.34/1.06    spl6_52 <=> sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)),
% 5.34/1.06    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 5.34/1.06  fof(f517,plain,(
% 5.34/1.06    spl6_31 <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1))),
% 5.34/1.06    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 5.34/1.06  fof(f1610,plain,(
% 5.34/1.06    sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | ~spl6_31),
% 5.34/1.06    inference(resolution,[],[f519,f107])).
% 5.34/1.06  fof(f519,plain,(
% 5.34/1.06    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl6_31),
% 5.34/1.06    inference(avatar_component_clause,[],[f517])).
% 5.34/1.06  fof(f2322,plain,(
% 5.34/1.06    spl6_10 | spl6_2 | ~spl6_36 | ~spl6_85),
% 5.34/1.06    inference(avatar_split_clause,[],[f2321,f2084,f618,f114,f168])).
% 5.34/1.06  fof(f168,plain,(
% 5.34/1.06    spl6_10 <=> r2_hidden(sK1,sK2)),
% 5.34/1.06    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 5.34/1.06  fof(f114,plain,(
% 5.34/1.06    spl6_2 <=> k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k2_enumset1(sK1,sK1,sK1,sK1)),
% 5.34/1.06    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 5.34/1.06  fof(f618,plain,(
% 5.34/1.06    spl6_36 <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))),
% 5.34/1.06    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 5.34/1.06  fof(f2084,plain,(
% 5.34/1.06    spl6_85 <=> sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))),
% 5.34/1.06    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).
% 5.34/1.06  fof(f2321,plain,(
% 5.34/1.06    r2_hidden(sK1,sK2) | (spl6_2 | ~spl6_36 | ~spl6_85)),
% 5.34/1.06    inference(subsumption_resolution,[],[f2320,f98])).
% 5.34/1.06  fof(f2320,plain,(
% 5.34/1.06    ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | r2_hidden(sK1,sK2) | (spl6_2 | ~spl6_36 | ~spl6_85)),
% 5.34/1.06    inference(forward_demodulation,[],[f2319,f2086])).
% 5.34/1.06  fof(f2086,plain,(
% 5.34/1.06    sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl6_85),
% 5.34/1.06    inference(avatar_component_clause,[],[f2084])).
% 5.34/1.06  fof(f2319,plain,(
% 5.34/1.06    r2_hidden(sK1,sK2) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | (spl6_2 | ~spl6_36 | ~spl6_85)),
% 5.34/1.06    inference(forward_demodulation,[],[f2318,f2086])).
% 5.34/1.06  fof(f2318,plain,(
% 5.34/1.06    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | (spl6_2 | ~spl6_36)),
% 5.34/1.06    inference(subsumption_resolution,[],[f1076,f620])).
% 5.34/1.06  fof(f620,plain,(
% 5.34/1.06    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl6_36),
% 5.34/1.06    inference(avatar_component_clause,[],[f618])).
% 5.34/1.06  fof(f1076,plain,(
% 5.34/1.06    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | spl6_2),
% 5.34/1.06    inference(equality_resolution,[],[f263])).
% 5.34/1.06  fof(f263,plain,(
% 5.34/1.06    ( ! [X1] : (k2_enumset1(sK1,sK1,sK1,sK1) != X1 | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),sK2) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),X1)) ) | spl6_2),
% 5.34/1.06    inference(superposition,[],[f116,f79])).
% 5.34/1.06  fof(f79,plain,(
% 5.34/1.06    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 5.34/1.06    inference(definition_unfolding,[],[f54,f41])).
% 5.34/1.06  fof(f41,plain,(
% 5.34/1.06    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.34/1.06    inference(cnf_transformation,[],[f3])).
% 5.34/1.06  fof(f3,axiom,(
% 5.34/1.06    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.34/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 5.34/1.06  fof(f54,plain,(
% 5.34/1.06    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 5.34/1.06    inference(cnf_transformation,[],[f25])).
% 5.34/1.06  fof(f25,plain,(
% 5.34/1.06    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.34/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).
% 5.34/1.06  % (13160)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 5.34/1.07  fof(f24,plain,(
% 5.34/1.07    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 5.34/1.07    introduced(choice_axiom,[])).
% 5.34/1.07  fof(f23,plain,(
% 5.34/1.07    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.34/1.07    inference(rectify,[],[f22])).
% 5.34/1.07  fof(f22,plain,(
% 5.34/1.07    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.34/1.07    inference(flattening,[],[f21])).
% 5.34/1.07  fof(f21,plain,(
% 5.34/1.07    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.34/1.07    inference(nnf_transformation,[],[f1])).
% 5.34/1.07  fof(f1,axiom,(
% 5.34/1.07    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 5.34/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 5.34/1.07  fof(f116,plain,(
% 5.34/1.07    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK1,sK1,sK1,sK1) | spl6_2),
% 5.34/1.07    inference(avatar_component_clause,[],[f114])).
% 5.34/1.07  fof(f2317,plain,(
% 5.34/1.07    spl6_9 | spl6_10 | spl6_1),
% 5.34/1.07    inference(avatar_split_clause,[],[f331,f109,f168,f164])).
% 5.34/1.07  fof(f109,plain,(
% 5.34/1.07    spl6_1 <=> k2_enumset1(sK0,sK0,sK0,sK1) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),
% 5.34/1.07    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 5.34/1.07  fof(f331,plain,(
% 5.34/1.07    r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | spl6_1),
% 5.34/1.07    inference(trivial_inequality_removal,[],[f319])).
% 5.34/1.07  fof(f319,plain,(
% 5.34/1.07    k2_enumset1(sK0,sK0,sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK1) | r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | spl6_1),
% 5.34/1.07    inference(superposition,[],[f111,f94])).
% 5.34/1.07  fof(f94,plain,(
% 5.34/1.07    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k3_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 5.34/1.07    inference(definition_unfolding,[],[f66,f67,f41,f67])).
% 5.34/1.08  fof(f66,plain,(
% 5.34/1.08    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 5.34/1.08    inference(cnf_transformation,[],[f34])).
% 5.34/1.08  fof(f34,plain,(
% 5.34/1.08    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 5.34/1.08    inference(flattening,[],[f33])).
% 5.34/1.08  fof(f33,plain,(
% 5.34/1.08    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 5.34/1.08    inference(nnf_transformation,[],[f10])).
% 5.34/1.08  fof(f10,axiom,(
% 5.34/1.08    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 5.34/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 5.34/1.08  fof(f111,plain,(
% 5.34/1.08    k2_enumset1(sK0,sK0,sK0,sK1) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) | spl6_1),
% 5.34/1.08    inference(avatar_component_clause,[],[f109])).
% 5.34/1.08  fof(f2236,plain,(
% 5.34/1.08    sK0 != sK5(sK0,sK0,k1_xboole_0) | sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | sK0 != sK3(sK0,k1_xboole_0) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | r2_hidden(sK5(sK0,sK0,k1_xboole_0),k1_xboole_0)),
% 5.34/1.08    introduced(theory_tautology_sat_conflict,[])).
% 5.34/1.08  fof(f2183,plain,(
% 5.34/1.08    spl6_85 | spl6_88 | ~spl6_36),
% 5.34/1.08    inference(avatar_split_clause,[],[f2171,f618,f2178,f2084])).
% 5.34/1.08  fof(f2178,plain,(
% 5.34/1.08    spl6_88 <=> sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))),
% 5.34/1.08    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).
% 5.34/1.08  fof(f2171,plain,(
% 5.34/1.08    sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl6_36),
% 5.34/1.08    inference(resolution,[],[f620,f107])).
% 5.34/1.08  fof(f2182,plain,(
% 5.34/1.08    sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | sK0 != sK3(sK0,k1_xboole_0) | ~r2_hidden(sK0,sK2) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)),
% 5.34/1.08    introduced(theory_tautology_sat_conflict,[])).
% 5.34/1.08  fof(f2127,plain,(
% 5.34/1.08    spl6_86 | spl6_87 | ~spl6_29),
% 5.34/1.08    inference(avatar_split_clause,[],[f2117,f502,f2124,f2120])).
% 5.34/1.08  fof(f2120,plain,(
% 5.34/1.08    spl6_86 <=> sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))),
% 5.34/1.08    introduced(avatar_definition,[new_symbols(naming,[spl6_86])])).
% 5.34/1.08  fof(f2124,plain,(
% 5.34/1.08    spl6_87 <=> sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))),
% 5.34/1.08    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).
% 5.34/1.08  fof(f502,plain,(
% 5.34/1.08    spl6_29 <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))),
% 5.34/1.08    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 5.34/1.08  fof(f2117,plain,(
% 5.34/1.08    sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl6_29),
% 5.34/1.08    inference(resolution,[],[f504,f107])).
% 5.34/1.08  fof(f504,plain,(
% 5.34/1.08    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl6_29),
% 5.34/1.08    inference(avatar_component_clause,[],[f502])).
% 5.34/1.08  fof(f2089,plain,(
% 5.34/1.08    sK1 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | sK1 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | sK1 != sK3(sK1,k1_xboole_0) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))),
% 5.34/1.08    introduced(theory_tautology_sat_conflict,[])).
% 5.34/1.08  fof(f2088,plain,(
% 5.34/1.08    spl6_85 | ~spl6_27),
% 5.34/1.08    inference(avatar_split_clause,[],[f2054,f490,f2084])).
% 5.34/1.08  fof(f490,plain,(
% 5.34/1.08    spl6_27 <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))),
% 5.34/1.08    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 5.34/1.08  fof(f2054,plain,(
% 5.34/1.08    sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl6_27),
% 5.34/1.08    inference(duplicate_literal_removal,[],[f2049])).
% 5.34/1.08  fof(f2049,plain,(
% 5.34/1.08    sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | sK1 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl6_27),
% 5.34/1.08    inference(resolution,[],[f492,f107])).
% 5.34/1.08  fof(f492,plain,(
% 5.34/1.08    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl6_27),
% 5.34/1.08    inference(avatar_component_clause,[],[f490])).
% 5.34/1.08  fof(f2010,plain,(
% 5.34/1.08    spl6_80 | ~spl6_25),
% 5.34/1.08    inference(avatar_split_clause,[],[f2003,f477,f2006])).
% 5.34/1.08  fof(f2003,plain,(
% 5.34/1.08    sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl6_25),
% 5.34/1.08    inference(duplicate_literal_removal,[],[f1998])).
% 5.34/1.08  fof(f1998,plain,(
% 5.34/1.08    sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl6_25),
% 5.34/1.08    inference(resolution,[],[f479,f107])).
% 5.34/1.08  fof(f479,plain,(
% 5.34/1.08    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl6_25),
% 5.34/1.08    inference(avatar_component_clause,[],[f477])).
% 5.34/1.09  fof(f1094,plain,(
% 5.34/1.09    ~spl6_29 | spl6_30 | spl6_1),
% 5.34/1.09    inference(avatar_split_clause,[],[f1091,f109,f506,f502])).
% 5.34/1.09  fof(f506,plain,(
% 5.34/1.09    spl6_30 <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)),
% 5.34/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 5.34/1.09  fof(f1091,plain,(
% 5.34/1.09    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | spl6_1),
% 5.34/1.09    inference(duplicate_literal_removal,[],[f1090])).
% 5.34/1.09  fof(f1090,plain,(
% 5.34/1.09    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | spl6_1),
% 5.34/1.09    inference(equality_resolution,[],[f264])).
% 5.34/1.09  fof(f264,plain,(
% 5.34/1.09    ( ! [X2] : (k2_enumset1(sK0,sK0,sK0,sK1) != X2 | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X2),sK2) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X2),k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X2),X2)) ) | spl6_1),
% 5.34/1.09    inference(superposition,[],[f111,f79])).
% 5.34/1.09  fof(f1072,plain,(
% 5.34/1.09    ~spl6_25 | ~spl6_34 | spl6_26 | spl6_3),
% 5.34/1.09    inference(avatar_split_clause,[],[f1068,f119,f481,f596,f477])).
% 5.34/1.09  fof(f481,plain,(
% 5.34/1.09    spl6_26 <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2)),
% 5.34/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 5.34/1.09  fof(f119,plain,(
% 5.34/1.09    spl6_3 <=> k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 5.34/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 5.34/1.09  fof(f1068,plain,(
% 5.34/1.09    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl6_3),
% 5.34/1.09    inference(equality_resolution,[],[f262])).
% 5.34/1.09  fof(f262,plain,(
% 5.34/1.09    ( ! [X0] : (k2_enumset1(sK0,sK0,sK0,sK0) != X0 | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),sK2) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),X0)) ) | spl6_3),
% 5.34/1.09    inference(superposition,[],[f121,f79])).
% 5.34/1.09  fof(f121,plain,(
% 5.34/1.09    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK0,sK0,sK0,sK0) | spl6_3),
% 5.34/1.09    inference(avatar_component_clause,[],[f119])).
% 5.34/1.09  fof(f1007,plain,(
% 5.34/1.09    spl6_22 | spl6_13 | spl6_21),
% 5.34/1.09    inference(avatar_split_clause,[],[f1006,f419,f241,f423])).
% 5.34/1.09  fof(f423,plain,(
% 5.34/1.09    spl6_22 <=> sK0 = sK5(sK0,sK0,k1_xboole_0)),
% 5.34/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 5.34/1.09  fof(f241,plain,(
% 5.34/1.09    spl6_13 <=> r2_hidden(sK0,k1_xboole_0)),
% 5.34/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 5.34/1.09  fof(f419,plain,(
% 5.34/1.09    spl6_21 <=> r2_hidden(sK5(sK0,sK0,k1_xboole_0),k1_xboole_0)),
% 5.34/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 5.34/1.09  fof(f1006,plain,(
% 5.34/1.09    sK0 = sK5(sK0,sK0,k1_xboole_0) | (spl6_13 | spl6_21)),
% 5.34/1.09    inference(subsumption_resolution,[],[f1005,f242])).
% 5.34/1.09  fof(f242,plain,(
% 5.34/1.09    ~r2_hidden(sK0,k1_xboole_0) | spl6_13),
% 5.34/1.09    inference(avatar_component_clause,[],[f241])).
% 5.34/1.09  fof(f1005,plain,(
% 5.34/1.09    sK0 = sK5(sK0,sK0,k1_xboole_0) | r2_hidden(sK0,k1_xboole_0) | spl6_21),
% 5.34/1.09    inference(resolution,[],[f420,f306])).
% 5.34/1.09  fof(f306,plain,(
% 5.34/1.09    ( ! [X6,X7] : (r2_hidden(sK5(X6,X6,X7),X7) | sK5(X6,X6,X7) = X6 | r2_hidden(X6,X7)) )),
% 5.34/1.09    inference(duplicate_literal_removal,[],[f289])).
% 5.34/1.09  fof(f289,plain,(
% 5.34/1.09    ( ! [X6,X7] : (r2_hidden(X6,X7) | sK5(X6,X6,X7) = X6 | sK5(X6,X6,X7) = X6 | r2_hidden(sK5(X6,X6,X7),X7)) )),
% 5.34/1.09    inference(superposition,[],[f98,f87])).
% 5.34/1.09  fof(f87,plain,(
% 5.34/1.09    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X0,X1) = X2 | sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 5.34/1.09    inference(definition_unfolding,[],[f58,f67])).
% 5.34/1.09  fof(f58,plain,(
% 5.34/1.09    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 5.34/1.09    inference(cnf_transformation,[],[f30])).
% 5.34/1.09  fof(f420,plain,(
% 5.34/1.09    ~r2_hidden(sK5(sK0,sK0,k1_xboole_0),k1_xboole_0) | spl6_21),
% 5.34/1.09    inference(avatar_component_clause,[],[f419])).
% 5.34/1.09  fof(f959,plain,(
% 5.34/1.09    spl6_15 | spl6_14 | spl6_18),
% 5.34/1.09    inference(avatar_split_clause,[],[f958,f374,f277,f281])).
% 5.34/1.09  fof(f281,plain,(
% 5.34/1.09    spl6_15 <=> sK1 = sK3(sK1,k1_xboole_0)),
% 5.34/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 5.34/1.09  fof(f277,plain,(
% 5.34/1.09    spl6_14 <=> r2_hidden(sK3(sK1,k1_xboole_0),k1_xboole_0)),
% 5.34/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 5.34/1.09  fof(f374,plain,(
% 5.34/1.09    spl6_18 <=> r2_hidden(sK1,k1_xboole_0)),
% 5.34/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 5.34/1.09  fof(f958,plain,(
% 5.34/1.09    sK1 = sK3(sK1,k1_xboole_0) | (spl6_14 | spl6_18)),
% 5.34/1.09    inference(subsumption_resolution,[],[f945,f375])).
% 5.34/1.09  fof(f375,plain,(
% 5.34/1.09    ~r2_hidden(sK1,k1_xboole_0) | spl6_18),
% 5.34/1.09    inference(avatar_component_clause,[],[f374])).
% 5.34/1.09  fof(f945,plain,(
% 5.34/1.09    sK1 = sK3(sK1,k1_xboole_0) | r2_hidden(sK1,k1_xboole_0) | spl6_14),
% 5.34/1.09    inference(resolution,[],[f278,f183])).
% 5.34/1.09  fof(f183,plain,(
% 5.34/1.09    ( ! [X4,X3] : (r2_hidden(sK3(X3,X4),X4) | sK3(X3,X4) = X3 | r2_hidden(X3,X4)) )),
% 5.34/1.09    inference(superposition,[],[f98,f74])).
% 5.34/1.09  fof(f74,plain,(
% 5.34/1.09    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = X1 | sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)) )),
% 5.34/1.09    inference(definition_unfolding,[],[f44,f68])).
% 5.34/1.09  fof(f44,plain,(
% 5.34/1.09    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)) )),
% 5.34/1.09    inference(cnf_transformation,[],[f19])).
% 5.34/1.09  fof(f278,plain,(
% 5.34/1.09    ~r2_hidden(sK3(sK1,k1_xboole_0),k1_xboole_0) | spl6_14),
% 5.34/1.09    inference(avatar_component_clause,[],[f277])).
% 5.34/1.09  fof(f905,plain,(
% 5.34/1.09    spl6_31 | spl6_4 | spl6_19),
% 5.34/1.09    inference(avatar_split_clause,[],[f515,f390,f124,f517])).
% 5.34/1.09  fof(f124,plain,(
% 5.34/1.09    spl6_4 <=> k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),
% 5.34/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 5.34/1.09  fof(f390,plain,(
% 5.34/1.09    spl6_19 <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)),
% 5.34/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 5.34/1.09  fof(f515,plain,(
% 5.34/1.09    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1)) | (spl6_4 | spl6_19)),
% 5.34/1.09    inference(subsumption_resolution,[],[f514,f391])).
% 5.34/1.09  fof(f391,plain,(
% 5.34/1.09    ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | spl6_19),
% 5.34/1.09    inference(avatar_component_clause,[],[f390])).
% 5.34/1.09  fof(f514,plain,(
% 5.34/1.09    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | spl6_4),
% 5.34/1.09    inference(equality_resolution,[],[f221])).
% 5.34/1.09  fof(f221,plain,(
% 5.34/1.09    ( ! [X3] : (k1_xboole_0 != X3 | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X3),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X3),X3)) ) | spl6_4),
% 5.34/1.09    inference(superposition,[],[f126,f81])).
% 5.34/1.09  fof(f81,plain,(
% 5.34/1.09    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 5.34/1.09    inference(definition_unfolding,[],[f52,f41])).
% 5.34/1.09  fof(f52,plain,(
% 5.34/1.09    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 5.34/1.09    inference(cnf_transformation,[],[f25])).
% 5.34/1.09  fof(f126,plain,(
% 5.34/1.09    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) | spl6_4),
% 5.34/1.09    inference(avatar_component_clause,[],[f124])).
% 5.34/1.09  fof(f902,plain,(
% 5.34/1.09    spl6_12 | spl6_6 | ~spl6_42),
% 5.34/1.09    inference(avatar_split_clause,[],[f901,f704,f138,f200])).
% 5.34/1.09  fof(f200,plain,(
% 5.34/1.09    spl6_12 <=> sK0 = sK3(sK0,k1_xboole_0)),
% 5.34/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 5.34/1.09  fof(f138,plain,(
% 5.34/1.09    spl6_6 <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 5.34/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 5.34/1.09  fof(f901,plain,(
% 5.34/1.09    sK0 = sK3(sK0,k1_xboole_0) | (spl6_6 | ~spl6_42)),
% 5.34/1.09    inference(subsumption_resolution,[],[f387,f830])).
% 5.34/1.09  fof(f830,plain,(
% 5.34/1.09    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | sK0 = X0) ) | ~spl6_42),
% 5.34/1.09    inference(resolution,[],[f757,f99])).
% 5.34/1.09  fof(f99,plain,(
% 5.34/1.09    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 5.34/1.09    inference(equality_resolution,[],[f76])).
% 5.34/1.09  fof(f76,plain,(
% 5.34/1.09    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 5.34/1.09    inference(definition_unfolding,[],[f42,f68])).
% 5.34/1.09  fof(f42,plain,(
% 5.34/1.09    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 5.34/1.09    inference(cnf_transformation,[],[f19])).
% 5.34/1.09  fof(f757,plain,(
% 5.34/1.09    ( ! [X1] : (r2_hidden(X1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(X1,k1_xboole_0)) ) | ~spl6_42),
% 5.34/1.09    inference(resolution,[],[f705,f158])).
% 5.34/1.09  fof(f158,plain,(
% 5.34/1.09    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X0) | ~r2_hidden(X2,k1_xboole_0)) )),
% 5.34/1.09    inference(superposition,[],[f102,f77])).
% 5.34/1.09  fof(f77,plain,(
% 5.34/1.09    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 5.34/1.09    inference(definition_unfolding,[],[f47,f41])).
% 5.34/1.09  fof(f47,plain,(
% 5.34/1.09    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 5.34/1.09    inference(cnf_transformation,[],[f20])).
% 5.34/1.09  fof(f20,plain,(
% 5.34/1.09    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 5.34/1.09    inference(nnf_transformation,[],[f2])).
% 5.34/1.09  fof(f2,axiom,(
% 5.34/1.09    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 5.34/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 5.34/1.09  fof(f102,plain,(
% 5.34/1.09    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X0)) )),
% 5.34/1.09    inference(equality_resolution,[],[f84])).
% 5.34/1.09  fof(f84,plain,(
% 5.34/1.09    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 5.34/1.09    inference(definition_unfolding,[],[f49,f41])).
% 5.34/1.09  fof(f49,plain,(
% 5.34/1.09    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 5.34/1.09    inference(cnf_transformation,[],[f25])).
% 5.34/1.09  fof(f705,plain,(
% 5.34/1.09    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK2) | ~spl6_42),
% 5.34/1.09    inference(avatar_component_clause,[],[f704])).
% 5.34/1.09  fof(f387,plain,(
% 5.34/1.09    sK0 = sK3(sK0,k1_xboole_0) | r2_hidden(sK3(sK0,k1_xboole_0),k1_xboole_0) | spl6_6),
% 5.34/1.09    inference(equality_resolution,[],[f257])).
% 5.34/1.09  fof(f257,plain,(
% 5.34/1.09    ( ! [X0] : (k1_xboole_0 != X0 | sK0 = sK3(sK0,X0) | r2_hidden(sK3(sK0,X0),X0)) ) | spl6_6),
% 5.34/1.09    inference(superposition,[],[f140,f74])).
% 5.34/1.09  fof(f140,plain,(
% 5.34/1.09    k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0) | spl6_6),
% 5.34/1.09    inference(avatar_component_clause,[],[f138])).
% 5.34/1.09  fof(f895,plain,(
% 5.34/1.09    sK0 != sK3(sK1,k1_xboole_0) | sK0 != sK3(sK0,k1_xboole_0) | ~r2_hidden(sK3(sK1,k1_xboole_0),k1_xboole_0) | r2_hidden(sK3(sK0,k1_xboole_0),k1_xboole_0)),
% 5.34/1.09    introduced(theory_tautology_sat_conflict,[])).
% 5.34/1.09  fof(f894,plain,(
% 5.34/1.09    sK0 != sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | sK0 != sK3(sK0,k1_xboole_0) | ~r2_hidden(sK0,sK2) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2)),
% 5.34/1.09    introduced(theory_tautology_sat_conflict,[])).
% 5.34/1.09  fof(f886,plain,(
% 5.34/1.09    sK0 != sK5(sK0,sK0,k1_xboole_0) | sK0 != sK3(sK0,k1_xboole_0) | ~r2_hidden(sK5(sK0,sK0,k1_xboole_0),k1_xboole_0) | r2_hidden(sK3(sK0,k1_xboole_0),k1_xboole_0)),
% 5.34/1.09    introduced(theory_tautology_sat_conflict,[])).
% 5.34/1.09  fof(f885,plain,(
% 5.34/1.09    spl6_53 | ~spl6_14 | ~spl6_42),
% 5.34/1.09    inference(avatar_split_clause,[],[f846,f704,f277,f882])).
% 5.34/1.09  fof(f882,plain,(
% 5.34/1.09    spl6_53 <=> sK0 = sK3(sK1,k1_xboole_0)),
% 5.34/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 5.34/1.09  fof(f846,plain,(
% 5.34/1.09    sK0 = sK3(sK1,k1_xboole_0) | (~spl6_14 | ~spl6_42)),
% 5.34/1.09    inference(resolution,[],[f830,f279])).
% 5.34/1.09  fof(f279,plain,(
% 5.34/1.09    r2_hidden(sK3(sK1,k1_xboole_0),k1_xboole_0) | ~spl6_14),
% 5.34/1.09    inference(avatar_component_clause,[],[f277])).
% 5.34/1.09  fof(f880,plain,(
% 5.34/1.09    spl6_52 | ~spl6_19 | ~spl6_42),
% 5.34/1.09    inference(avatar_split_clause,[],[f851,f704,f390,f877])).
% 5.34/1.09  fof(f851,plain,(
% 5.34/1.09    sK0 = sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | (~spl6_19 | ~spl6_42)),
% 5.34/1.09    inference(resolution,[],[f830,f392])).
% 5.34/1.09  fof(f392,plain,(
% 5.34/1.09    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | ~spl6_19),
% 5.34/1.09    inference(avatar_component_clause,[],[f390])).
% 5.34/1.09  fof(f865,plain,(
% 5.34/1.09    spl6_22 | ~spl6_21 | ~spl6_42),
% 5.34/1.09    inference(avatar_split_clause,[],[f853,f704,f419,f423])).
% 5.34/1.09  fof(f853,plain,(
% 5.34/1.09    sK0 = sK5(sK0,sK0,k1_xboole_0) | (~spl6_21 | ~spl6_42)),
% 5.34/1.09    inference(resolution,[],[f830,f421])).
% 5.34/1.09  fof(f421,plain,(
% 5.34/1.09    r2_hidden(sK5(sK0,sK0,k1_xboole_0),k1_xboole_0) | ~spl6_21),
% 5.34/1.09    inference(avatar_component_clause,[],[f419])).
% 5.34/1.09  fof(f864,plain,(
% 5.34/1.09    ~spl6_13 | ~spl6_9 | ~spl6_42),
% 5.34/1.09    inference(avatar_split_clause,[],[f766,f704,f164,f241])).
% 5.34/1.09  fof(f766,plain,(
% 5.34/1.09    ~r2_hidden(sK0,k1_xboole_0) | (~spl6_9 | ~spl6_42)),
% 5.34/1.09    inference(resolution,[],[f758,f165])).
% 5.34/1.09  fof(f165,plain,(
% 5.34/1.09    r2_hidden(sK0,sK2) | ~spl6_9),
% 5.34/1.09    inference(avatar_component_clause,[],[f164])).
% 5.34/1.09  fof(f758,plain,(
% 5.34/1.09    ( ! [X2] : (~r2_hidden(X2,sK2) | ~r2_hidden(X2,k1_xboole_0)) ) | ~spl6_42),
% 5.34/1.09    inference(resolution,[],[f705,f157])).
% 5.34/1.09  fof(f157,plain,(
% 5.34/1.09    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,k1_xboole_0)) )),
% 5.34/1.09    inference(superposition,[],[f101,f77])).
% 5.34/1.09  fof(f101,plain,(
% 5.34/1.09    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 5.34/1.09    inference(equality_resolution,[],[f83])).
% 5.34/1.09  fof(f83,plain,(
% 5.34/1.09    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 5.34/1.09    inference(definition_unfolding,[],[f50,f41])).
% 5.34/1.09  fof(f50,plain,(
% 5.34/1.09    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 5.34/1.09    inference(cnf_transformation,[],[f25])).
% 5.34/1.09  fof(f862,plain,(
% 5.34/1.09    sK0 != sK3(sK0,k1_xboole_0) | r2_hidden(sK0,k1_xboole_0) | ~r2_hidden(sK3(sK0,k1_xboole_0),k1_xboole_0)),
% 5.34/1.09    introduced(theory_tautology_sat_conflict,[])).
% 5.34/1.09  fof(f793,plain,(
% 5.34/1.09    ~spl6_18 | ~spl6_42 | spl6_49),
% 5.34/1.09    inference(avatar_contradiction_clause,[],[f789])).
% 5.34/1.09  fof(f789,plain,(
% 5.34/1.09    $false | (~spl6_18 | ~spl6_42 | spl6_49)),
% 5.34/1.09    inference(unit_resulting_resolution,[],[f376,f705,f741,f158])).
% 5.34/1.09  fof(f741,plain,(
% 5.34/1.09    ~r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | spl6_49),
% 5.34/1.09    inference(avatar_component_clause,[],[f740])).
% 5.34/1.09  fof(f740,plain,(
% 5.34/1.09    spl6_49 <=> r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 5.34/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 5.34/1.09  fof(f376,plain,(
% 5.34/1.09    r2_hidden(sK1,k1_xboole_0) | ~spl6_18),
% 5.34/1.09    inference(avatar_component_clause,[],[f374])).
% 5.34/1.09  fof(f788,plain,(
% 5.34/1.09    spl6_35 | ~spl6_49),
% 5.34/1.09    inference(avatar_contradiction_clause,[],[f787])).
% 5.34/1.09  fof(f787,plain,(
% 5.34/1.09    $false | (spl6_35 | ~spl6_49)),
% 5.34/1.09    inference(subsumption_resolution,[],[f782,f607])).
% 5.34/1.09  fof(f607,plain,(
% 5.34/1.09    sK0 != sK1 | spl6_35),
% 5.34/1.09    inference(avatar_component_clause,[],[f606])).
% 5.34/1.09  fof(f606,plain,(
% 5.34/1.09    spl6_35 <=> sK0 = sK1),
% 5.34/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 5.34/1.09  fof(f782,plain,(
% 5.34/1.09    sK0 = sK1 | ~spl6_49),
% 5.34/1.09    inference(duplicate_literal_removal,[],[f778])).
% 5.34/1.09  fof(f778,plain,(
% 5.34/1.09    sK0 = sK1 | sK0 = sK1 | ~spl6_49),
% 5.34/1.09    inference(resolution,[],[f742,f107])).
% 5.34/1.09  fof(f742,plain,(
% 5.34/1.09    r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl6_49),
% 5.34/1.09    inference(avatar_component_clause,[],[f740])).
% 5.34/1.09  fof(f707,plain,(
% 5.34/1.09    ~spl6_42 | spl6_5 | ~spl6_17),
% 5.34/1.09    inference(avatar_split_clause,[],[f664,f349,f134,f704])).
% 5.34/1.09  fof(f134,plain,(
% 5.34/1.09    spl6_5 <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),
% 5.34/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 5.34/1.09  fof(f349,plain,(
% 5.34/1.09    spl6_17 <=> k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 5.34/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 5.34/1.09  fof(f664,plain,(
% 5.34/1.09    ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK2) | (spl6_5 | ~spl6_17)),
% 5.34/1.09    inference(superposition,[],[f136,f350])).
% 5.34/1.09  fof(f350,plain,(
% 5.34/1.09    k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl6_17),
% 5.34/1.09    inference(avatar_component_clause,[],[f349])).
% 5.34/1.09  fof(f136,plain,(
% 5.34/1.09    ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),sK2) | spl6_5),
% 5.34/1.09    inference(avatar_component_clause,[],[f134])).
% 5.34/1.09  fof(f657,plain,(
% 5.34/1.09    spl6_37 | ~spl6_32 | spl6_33),
% 5.34/1.09    inference(avatar_split_clause,[],[f624,f559,f555,f626])).
% 5.34/1.09  fof(f626,plain,(
% 5.34/1.09    spl6_37 <=> sK0 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1))),
% 5.34/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 5.34/1.09  fof(f555,plain,(
% 5.34/1.09    spl6_32 <=> r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))),
% 5.34/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 5.34/1.09  fof(f559,plain,(
% 5.34/1.09    spl6_33 <=> sK1 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1))),
% 5.34/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 5.34/1.09  fof(f624,plain,(
% 5.34/1.09    sK0 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1)) | (~spl6_32 | spl6_33)),
% 5.34/1.09    inference(subsumption_resolution,[],[f622,f560])).
% 5.34/1.09  fof(f560,plain,(
% 5.34/1.09    sK1 != sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1)) | spl6_33),
% 5.34/1.09    inference(avatar_component_clause,[],[f559])).
% 5.34/1.09  fof(f622,plain,(
% 5.34/1.09    sK0 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1)) | sK1 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl6_32),
% 5.34/1.09    inference(resolution,[],[f557,f107])).
% 5.34/1.09  fof(f557,plain,(
% 5.34/1.09    r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl6_32),
% 5.34/1.09    inference(avatar_component_clause,[],[f555])).
% 5.34/1.09  fof(f651,plain,(
% 5.34/1.09    sK0 != sK1 | r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2)),
% 5.34/1.09    introduced(theory_tautology_sat_conflict,[])).
% 5.34/1.09  fof(f645,plain,(
% 5.34/1.09    sK0 != sK1 | k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 5.34/1.09    introduced(theory_tautology_sat_conflict,[])).
% 5.34/1.09  fof(f644,plain,(
% 5.34/1.09    spl6_16 | ~spl6_33),
% 5.34/1.09    inference(avatar_contradiction_clause,[],[f643])).
% 5.34/1.09  fof(f643,plain,(
% 5.34/1.09    $false | (spl6_16 | ~spl6_33)),
% 5.34/1.09    inference(subsumption_resolution,[],[f642,f104])).
% 5.34/1.09  fof(f104,plain,(
% 5.34/1.09    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 5.34/1.09    inference(equality_resolution,[],[f103])).
% 5.34/1.09  fof(f103,plain,(
% 5.34/1.09    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 5.34/1.09    inference(equality_resolution,[],[f88])).
% 5.34/1.09  fof(f88,plain,(
% 5.34/1.09    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 5.34/1.09    inference(definition_unfolding,[],[f57,f67])).
% 5.34/1.09  fof(f57,plain,(
% 5.34/1.09    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 5.34/1.09    inference(cnf_transformation,[],[f30])).
% 5.34/1.09  fof(f642,plain,(
% 5.34/1.09    ~r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK1)) | (spl6_16 | ~spl6_33)),
% 5.34/1.09    inference(subsumption_resolution,[],[f640,f346])).
% 5.34/1.09  fof(f346,plain,(
% 5.34/1.09    k2_enumset1(sK0,sK0,sK0,sK1) != k2_enumset1(sK1,sK1,sK1,sK1) | spl6_16),
% 5.34/1.09    inference(avatar_component_clause,[],[f344])).
% 5.34/1.09  fof(f344,plain,(
% 5.34/1.09    spl6_16 <=> k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK1,sK1,sK1,sK1)),
% 5.34/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 5.34/1.09  fof(f640,plain,(
% 5.34/1.09    k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK1,sK1,sK1,sK1) | ~r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl6_33),
% 5.34/1.09    inference(trivial_inequality_removal,[],[f639])).
% 5.34/1.09  fof(f639,plain,(
% 5.34/1.09    sK1 != sK1 | k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK1,sK1,sK1,sK1) | ~r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl6_33),
% 5.34/1.09    inference(superposition,[],[f73,f561])).
% 5.34/1.09  fof(f561,plain,(
% 5.34/1.09    sK1 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl6_33),
% 5.34/1.09    inference(avatar_component_clause,[],[f559])).
% 5.34/1.09  fof(f73,plain,(
% 5.34/1.09    ( ! [X0,X1] : (sK3(X0,X1) != X0 | k2_enumset1(X0,X0,X0,X0) = X1 | ~r2_hidden(sK3(X0,X1),X1)) )),
% 5.34/1.09    inference(definition_unfolding,[],[f45,f68])).
% 5.34/1.09  fof(f45,plain,(
% 5.34/1.09    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) )),
% 5.34/1.09    inference(cnf_transformation,[],[f19])).
% 5.34/1.09  fof(f634,plain,(
% 5.34/1.09    spl6_29 | spl6_1),
% 5.34/1.09    inference(avatar_split_clause,[],[f633,f109,f502])).
% 5.34/1.09  fof(f633,plain,(
% 5.34/1.09    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | spl6_1),
% 5.34/1.09    inference(duplicate_literal_removal,[],[f632])).
% 5.34/1.09  fof(f632,plain,(
% 5.34/1.09    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | spl6_1),
% 5.34/1.09    inference(equality_resolution,[],[f220])).
% 5.34/1.09  fof(f220,plain,(
% 5.34/1.09    ( ! [X2] : (k2_enumset1(sK0,sK0,sK0,sK1) != X2 | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X2),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X2),X2)) ) | spl6_1),
% 5.34/1.09    inference(superposition,[],[f111,f81])).
% 5.34/1.09  fof(f621,plain,(
% 5.34/1.09    spl6_27 | spl6_36 | spl6_2),
% 5.34/1.09    inference(avatar_split_clause,[],[f615,f114,f618,f490])).
% 5.34/1.09  fof(f615,plain,(
% 5.34/1.09    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | spl6_2),
% 5.34/1.09    inference(equality_resolution,[],[f219])).
% 5.34/1.09  fof(f219,plain,(
% 5.34/1.09    ( ! [X1] : (k2_enumset1(sK1,sK1,sK1,sK1) != X1 | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),X1)) ) | spl6_2),
% 5.34/1.09    inference(superposition,[],[f116,f81])).
% 5.34/1.09  fof(f609,plain,(
% 5.34/1.09    spl6_35 | ~spl6_16),
% 5.34/1.09    inference(avatar_split_clause,[],[f601,f344,f606])).
% 5.34/1.09  fof(f601,plain,(
% 5.34/1.09    sK0 = sK1 | ~spl6_16),
% 5.34/1.09    inference(resolution,[],[f570,f106])).
% 5.34/1.09  fof(f106,plain,(
% 5.34/1.09    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 5.34/1.09    inference(equality_resolution,[],[f105])).
% 5.34/1.09  fof(f105,plain,(
% 5.34/1.09    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 5.34/1.09    inference(equality_resolution,[],[f89])).
% 5.34/1.09  fof(f89,plain,(
% 5.34/1.09    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 5.34/1.09    inference(definition_unfolding,[],[f56,f67])).
% 5.34/1.09  fof(f56,plain,(
% 5.34/1.09    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 5.34/1.09    inference(cnf_transformation,[],[f30])).
% 5.34/1.09  fof(f570,plain,(
% 5.34/1.09    ( ! [X3] : (~r2_hidden(X3,k2_enumset1(sK0,sK0,sK0,sK1)) | sK1 = X3) ) | ~spl6_16),
% 5.34/1.09    inference(superposition,[],[f99,f345])).
% 5.34/1.09  fof(f345,plain,(
% 5.34/1.09    k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl6_16),
% 5.34/1.09    inference(avatar_component_clause,[],[f344])).
% 5.34/1.09  fof(f599,plain,(
% 5.34/1.09    spl6_25 | spl6_34 | spl6_3),
% 5.34/1.09    inference(avatar_split_clause,[],[f593,f119,f596,f477])).
% 5.34/1.09  fof(f593,plain,(
% 5.34/1.09    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl6_3),
% 5.34/1.09    inference(equality_resolution,[],[f218])).
% 5.34/1.09  fof(f218,plain,(
% 5.34/1.09    ( ! [X0] : (k2_enumset1(sK0,sK0,sK0,sK0) != X0 | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),X0)) ) | spl6_3),
% 5.34/1.09    inference(superposition,[],[f121,f81])).
% 5.34/1.09  fof(f562,plain,(
% 5.34/1.09    spl6_32 | spl6_33 | spl6_16),
% 5.34/1.09    inference(avatar_split_clause,[],[f553,f344,f559,f555])).
% 5.34/1.09  fof(f553,plain,(
% 5.34/1.09    sK1 = sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK3(sK1,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | spl6_16),
% 5.34/1.09    inference(equality_resolution,[],[f383])).
% 5.34/1.09  fof(f383,plain,(
% 5.34/1.09    ( ! [X0] : (k2_enumset1(sK0,sK0,sK0,sK1) != X0 | sK1 = sK3(sK1,X0) | r2_hidden(sK3(sK1,X0),X0)) ) | spl6_16),
% 5.34/1.09    inference(superposition,[],[f346,f74])).
% 5.34/1.09  fof(f497,plain,(
% 5.34/1.09    spl6_27 | ~spl6_28 | spl6_2),
% 5.34/1.09    inference(avatar_split_clause,[],[f487,f114,f494,f490])).
% 5.34/1.09  fof(f494,plain,(
% 5.34/1.09    spl6_28 <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)),
% 5.34/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 5.34/1.09  fof(f487,plain,(
% 5.34/1.09    ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | spl6_2),
% 5.34/1.09    inference(equality_resolution,[],[f207])).
% 5.34/1.09  fof(f207,plain,(
% 5.34/1.09    ( ! [X1] : (k2_enumset1(sK1,sK1,sK1,sK1) != X1 | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),sK2) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),X1)) ) | spl6_2),
% 5.34/1.09    inference(superposition,[],[f116,f80])).
% 5.34/1.09  fof(f80,plain,(
% 5.34/1.09    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 5.34/1.09    inference(definition_unfolding,[],[f53,f41])).
% 5.34/1.09  fof(f53,plain,(
% 5.34/1.09    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 5.34/1.09    inference(cnf_transformation,[],[f25])).
% 5.34/1.09  fof(f484,plain,(
% 5.34/1.09    spl6_25 | ~spl6_26 | spl6_3),
% 5.34/1.09    inference(avatar_split_clause,[],[f474,f119,f481,f477])).
% 5.34/1.09  fof(f474,plain,(
% 5.34/1.09    ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl6_3),
% 5.34/1.09    inference(equality_resolution,[],[f206])).
% 5.34/1.09  fof(f206,plain,(
% 5.34/1.09    ( ! [X0] : (k2_enumset1(sK0,sK0,sK0,sK0) != X0 | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),sK2) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),X0)) ) | spl6_3),
% 5.34/1.09    inference(superposition,[],[f121,f80])).
% 5.34/1.09  fof(f397,plain,(
% 5.34/1.09    spl6_19 | ~spl6_20 | spl6_4),
% 5.34/1.09    inference(avatar_split_clause,[],[f388,f124,f394,f390])).
% 5.34/1.09  fof(f394,plain,(
% 5.34/1.09    spl6_20 <=> r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2)),
% 5.34/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 5.34/1.09  fof(f388,plain,(
% 5.34/1.09    ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | spl6_4),
% 5.34/1.09    inference(equality_resolution,[],[f209])).
% 5.34/1.09  fof(f209,plain,(
% 5.34/1.09    ( ! [X3] : (k1_xboole_0 != X3 | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X3),sK2) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X3),X3)) ) | spl6_4),
% 5.34/1.09    inference(superposition,[],[f126,f80])).
% 5.34/1.09  fof(f246,plain,(
% 5.34/1.09    spl6_13 | ~spl6_6),
% 5.34/1.09    inference(avatar_split_clause,[],[f237,f138,f241])).
% 5.34/1.09  fof(f237,plain,(
% 5.34/1.09    r2_hidden(sK0,k1_xboole_0) | ~spl6_6),
% 5.34/1.09    inference(superposition,[],[f104,f139])).
% 5.34/1.09  fof(f139,plain,(
% 5.34/1.09    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl6_6),
% 5.34/1.09    inference(avatar_component_clause,[],[f138])).
% 5.34/1.09  fof(f171,plain,(
% 5.34/1.09    ~spl6_9 | ~spl6_10 | spl6_5),
% 5.34/1.09    inference(avatar_split_clause,[],[f159,f134,f168,f164])).
% 5.34/1.09  fof(f159,plain,(
% 5.34/1.09    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | spl6_5),
% 5.34/1.09    inference(resolution,[],[f91,f136])).
% 5.34/1.09  fof(f152,plain,(
% 5.34/1.09    ~spl6_5 | spl6_4),
% 5.34/1.09    inference(avatar_split_clause,[],[f132,f124,f134])).
% 5.34/1.09  fof(f132,plain,(
% 5.34/1.09    ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),sK2) | spl6_4),
% 5.34/1.09    inference(trivial_inequality_removal,[],[f131])).
% 5.34/1.09  fof(f131,plain,(
% 5.34/1.09    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),sK2) | spl6_4),
% 5.34/1.09    inference(superposition,[],[f126,f77])).
% 5.34/1.09  fof(f127,plain,(
% 5.34/1.09    ~spl6_4),
% 5.34/1.09    inference(avatar_split_clause,[],[f72,f124])).
% 5.34/1.09  fof(f72,plain,(
% 5.34/1.09    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),
% 5.34/1.09    inference(definition_unfolding,[],[f35,f41,f67])).
% 5.34/1.09  fof(f35,plain,(
% 5.34/1.09    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 5.34/1.09    inference(cnf_transformation,[],[f15])).
% 5.34/1.09  fof(f15,plain,(
% 5.34/1.09    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 5.34/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).
% 5.34/1.09  fof(f14,plain,(
% 5.34/1.09    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) => (k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 5.34/1.09    introduced(choice_axiom,[])).
% 5.34/1.09  fof(f13,plain,(
% 5.34/1.09    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2))),
% 5.34/1.09    inference(ennf_transformation,[],[f12])).
% 5.34/1.09  fof(f12,negated_conjecture,(
% 5.34/1.09    ~! [X0,X1,X2] : ~(k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2))),
% 5.34/1.09    inference(negated_conjecture,[],[f11])).
% 5.34/1.09  fof(f11,conjecture,(
% 5.34/1.09    ! [X0,X1,X2] : ~(k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2))),
% 5.34/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_zfmisc_1)).
% 5.34/1.09  fof(f122,plain,(
% 5.34/1.09    ~spl6_3),
% 5.34/1.09    inference(avatar_split_clause,[],[f71,f119])).
% 5.34/1.09  fof(f71,plain,(
% 5.34/1.09    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK0,sK0,sK0,sK0)),
% 5.34/1.09    inference(definition_unfolding,[],[f36,f41,f67,f68])).
% 5.34/1.09  fof(f36,plain,(
% 5.34/1.09    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)),
% 5.34/1.09    inference(cnf_transformation,[],[f15])).
% 5.34/1.09  fof(f117,plain,(
% 5.34/1.09    ~spl6_2),
% 5.34/1.09    inference(avatar_split_clause,[],[f70,f114])).
% 5.34/1.09  fof(f70,plain,(
% 5.34/1.09    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK1,sK1,sK1,sK1)),
% 5.34/1.09    inference(definition_unfolding,[],[f37,f41,f67,f68])).
% 5.34/1.09  fof(f37,plain,(
% 5.34/1.09    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)),
% 5.34/1.09    inference(cnf_transformation,[],[f15])).
% 5.34/1.09  fof(f112,plain,(
% 5.34/1.09    ~spl6_1),
% 5.34/1.09    inference(avatar_split_clause,[],[f69,f109])).
% 5.34/1.09  fof(f69,plain,(
% 5.34/1.09    k2_enumset1(sK0,sK0,sK0,sK1) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),
% 5.34/1.09    inference(definition_unfolding,[],[f38,f67,f41,f67])).
% 5.34/1.09  fof(f38,plain,(
% 5.34/1.09    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 5.34/1.09    inference(cnf_transformation,[],[f15])).
% 5.34/1.09  % SZS output end Proof for theBenchmark
% 5.34/1.09  % (12995)------------------------------
% 5.34/1.09  % (12995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.34/1.09  % (12995)Termination reason: Refutation
% 5.34/1.09  
% 5.34/1.09  % (12995)Memory used [KB]: 12920
% 5.34/1.09  % (12995)Time elapsed: 0.442 s
% 5.34/1.09  % (12995)------------------------------
% 5.34/1.09  % (12995)------------------------------
% 5.34/1.09  % (12944)Time limit reached!
% 5.34/1.09  % (12944)------------------------------
% 5.34/1.09  % (12944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.34/1.09  % (12936)Success in time 0.714 s
%------------------------------------------------------------------------------
