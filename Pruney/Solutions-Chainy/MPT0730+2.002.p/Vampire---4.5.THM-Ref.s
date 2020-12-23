%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:13 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 264 expanded)
%              Number of leaves         :   29 (  87 expanded)
%              Depth                    :   12
%              Number of atoms          :  322 ( 564 expanded)
%              Number of equality atoms :   62 ( 197 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f492,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f122,f123,f189,f273,f443,f459,f465,f491])).

fof(f491,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f490])).

fof(f490,plain,
    ( $false
    | spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f486,f120])).

fof(f120,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl4_4
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f486,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl4_3 ),
    inference(resolution,[],[f475,f98])).

fof(f98,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f63,f88])).

fof(f88,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f64,f87])).

fof(f87,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f66,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f66,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f475,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2))))
        | ~ r2_hidden(sK1,X0) )
    | spl4_3 ),
    inference(resolution,[],[f117,f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f117,plain,
    ( ~ r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2))))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl4_3
  <=> r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f465,plain,
    ( spl4_4
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f462,f270,f119])).

fof(f270,plain,
    ( spl4_7
  <=> sP0(k2_enumset1(sK2,sK2,sK2,sK2),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f462,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl4_7 ),
    inference(resolution,[],[f272,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X0)
        & r2_hidden(X1,X2) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X1,X2,X0] :
      ( ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ sP0(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X1,X2,X0] :
      ( ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ sP0(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f272,plain,
    ( sP0(k2_enumset1(sK2,sK2,sK2,sK2),sK1,sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f270])).

fof(f459,plain,
    ( spl4_2
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f458])).

fof(f458,plain,
    ( $false
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f455,f102])).

fof(f102,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f455,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl4_2
    | ~ spl4_6 ),
    inference(resolution,[],[f449,f454])).

fof(f454,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f453,f112])).

fof(f112,plain,
    ( sK1 != sK2
    | spl4_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl4_2
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f453,plain,
    ( sK1 = sK2
    | ~ r1_tarski(sK2,sK1)
    | ~ spl4_6 ),
    inference(resolution,[],[f450,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f450,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f268,f145])).

fof(f145,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k2_enumset1(X1,X1,X1,X1))
      | r1_tarski(X2,X1) ) ),
    inference(superposition,[],[f68,f97])).

fof(f97,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f62,f88])).

fof(f62,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f268,plain,
    ( r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl4_6
  <=> r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f449,plain,
    ( ! [X10] :
        ( r1_tarski(sK2,X10)
        | ~ r1_tarski(sK1,X10) )
    | ~ spl4_6 ),
    inference(resolution,[],[f268,f172])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0))
      | ~ r1_tarski(X2,X1)
      | r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f81,f96])).

fof(f96,plain,(
    ! [X0] : k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f61,f89])).

fof(f89,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f65,f87])).

fof(f65,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f61,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).

fof(f443,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f442])).

fof(f442,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f441,f102])).

fof(f441,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl4_5 ),
    inference(resolution,[],[f439,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f439,plain,
    ( r2_hidden(sK2,sK2)
    | spl4_5 ),
    inference(duplicate_literal_removal,[],[f438])).

fof(f438,plain,
    ( r2_hidden(sK2,sK2)
    | r2_hidden(sK2,sK2)
    | spl4_5 ),
    inference(resolution,[],[f215,f264])).

fof(f264,plain,
    ( ~ r1_xboole_0(sK2,k2_enumset1(sK2,sK2,sK2,sK2))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl4_5
  <=> r1_xboole_0(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f215,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_enumset1(X1,X1,X1,X2))
      | r2_hidden(X2,X0)
      | r2_hidden(X1,X0) ) ),
    inference(trivial_inequality_removal,[],[f214])).

fof(f214,plain,(
    ! [X2,X0,X1] :
      ( X0 != X0
      | r1_xboole_0(X0,k2_enumset1(X1,X1,X1,X2))
      | r2_hidden(X2,X0)
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f73,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_enumset1(X0,X0,X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f82,f87])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f273,plain,
    ( ~ spl4_5
    | spl4_6
    | spl4_7
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f259,f115,f270,f266,f262])).

fof(f259,plain,
    ( sP0(k2_enumset1(sK2,sK2,sK2,sK2),sK1,sK2)
    | r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ r1_xboole_0(sK2,k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ spl4_3 ),
    inference(resolution,[],[f101,f116])).

fof(f116,plain,
    ( r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2))))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_tarski(k2_enumset1(X0,X0,X0,X1)))
      | sP0(X1,X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f85,f88])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | sP0(X1,X2,X0)
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | sP0(X1,X2,X0)
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_folding,[],[f36,f37])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).

fof(f189,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f108,f95])).

fof(f95,plain,(
    ! [X0] : r2_hidden(X0,k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f57,f91])).

fof(f91,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f60,f88,f90])).

fof(f90,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f59,f87])).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f60,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f57,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f108,plain,
    ( ~ r2_hidden(sK1,k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK1,sK1,sK1,sK1))))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_1
  <=> r2_hidden(sK1,k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK1,sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f123,plain,
    ( spl4_3
    | spl4_4
    | spl4_2 ),
    inference(avatar_split_clause,[],[f94,f110,f119,f115])).

fof(f94,plain,
    ( sK1 = sK2
    | r2_hidden(sK1,sK2)
    | r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f53,f91])).

fof(f53,plain,
    ( sK1 = sK2
    | r2_hidden(sK1,sK2)
    | r2_hidden(sK1,k1_ordinal1(sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ( sK1 != sK2
        & ~ r2_hidden(sK1,sK2) )
      | ~ r2_hidden(sK1,k1_ordinal1(sK2)) )
    & ( sK1 = sK2
      | r2_hidden(sK1,sK2)
      | r2_hidden(sK1,k1_ordinal1(sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f40,f41])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( ( ( X0 != X1
            & ~ r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_ordinal1(X1)) )
        & ( X0 = X1
          | r2_hidden(X0,X1)
          | r2_hidden(X0,k1_ordinal1(X1)) ) )
   => ( ( ( sK1 != sK2
          & ~ r2_hidden(sK1,sK2) )
        | ~ r2_hidden(sK1,k1_ordinal1(sK2)) )
      & ( sK1 = sK2
        | r2_hidden(sK1,sK2)
        | r2_hidden(sK1,k1_ordinal1(sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k1_ordinal1(X1)) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k1_ordinal1(X1)) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <~> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,k1_ordinal1(X1))
      <=> ( X0 = X1
          | r2_hidden(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f122,plain,
    ( ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f93,f119,f115])).

fof(f93,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f54,f91])).

fof(f54,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,k1_ordinal1(sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f113,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f104,f110,f106])).

fof(f104,plain,
    ( sK1 != sK2
    | ~ r2_hidden(sK1,k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK1,sK1,sK1,sK1)))) ),
    inference(inner_rewriting,[],[f92])).

fof(f92,plain,
    ( sK1 != sK2
    | ~ r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f55,f91])).

fof(f55,plain,
    ( sK1 != sK2
    | ~ r2_hidden(sK1,k1_ordinal1(sK2)) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:27:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (26285)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (26284)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (26284)Refutation not found, incomplete strategy% (26284)------------------------------
% 0.20/0.53  % (26284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26284)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26284)Memory used [KB]: 1663
% 0.20/0.53  % (26284)Time elapsed: 0.102 s
% 0.20/0.53  % (26284)------------------------------
% 0.20/0.53  % (26284)------------------------------
% 0.20/0.53  % (26313)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (26297)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (26288)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (26304)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.38/0.54  % (26293)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.38/0.54  % (26291)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.38/0.54  % (26292)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.38/0.54  % (26293)Refutation not found, incomplete strategy% (26293)------------------------------
% 1.38/0.54  % (26293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (26311)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.38/0.54  % (26312)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.38/0.54  % (26294)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.38/0.55  % (26306)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.38/0.55  % (26294)Refutation not found, incomplete strategy% (26294)------------------------------
% 1.38/0.55  % (26294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (26307)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.38/0.55  % (26310)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.38/0.55  % (26294)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (26294)Memory used [KB]: 10618
% 1.38/0.55  % (26294)Time elapsed: 0.123 s
% 1.38/0.55  % (26294)------------------------------
% 1.38/0.55  % (26294)------------------------------
% 1.38/0.55  % (26293)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (26293)Memory used [KB]: 10618
% 1.38/0.55  % (26293)Time elapsed: 0.131 s
% 1.38/0.55  % (26293)------------------------------
% 1.38/0.55  % (26293)------------------------------
% 1.38/0.55  % (26305)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.38/0.55  % (26298)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.38/0.55  % (26303)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.38/0.55  % (26302)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.38/0.56  % (26296)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.55/0.56  % (26286)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.55/0.56  % (26287)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.55/0.56  % (26289)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.55/0.56  % (26290)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.55/0.57  % (26309)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.55/0.57  % (26308)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.55/0.57  % (26301)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.55/0.58  % (26300)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.55/0.59  % (26299)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.55/0.59  % (26301)Refutation not found, incomplete strategy% (26301)------------------------------
% 1.55/0.59  % (26301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.59  % (26301)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.59  
% 1.55/0.59  % (26301)Memory used [KB]: 10618
% 1.55/0.59  % (26301)Time elapsed: 0.177 s
% 1.55/0.59  % (26301)------------------------------
% 1.55/0.59  % (26301)------------------------------
% 1.55/0.59  % (26295)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.55/0.59  % (26295)Refutation not found, incomplete strategy% (26295)------------------------------
% 1.55/0.59  % (26295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.59  % (26295)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.59  
% 1.55/0.59  % (26295)Memory used [KB]: 10618
% 1.55/0.59  % (26295)Time elapsed: 0.174 s
% 1.55/0.59  % (26295)------------------------------
% 1.55/0.59  % (26295)------------------------------
% 1.55/0.60  % (26311)Refutation found. Thanks to Tanya!
% 1.55/0.60  % SZS status Theorem for theBenchmark
% 1.55/0.61  % SZS output start Proof for theBenchmark
% 1.55/0.61  fof(f492,plain,(
% 1.55/0.61    $false),
% 1.55/0.61    inference(avatar_sat_refutation,[],[f113,f122,f123,f189,f273,f443,f459,f465,f491])).
% 1.55/0.61  fof(f491,plain,(
% 1.55/0.61    spl4_3 | ~spl4_4),
% 1.55/0.61    inference(avatar_contradiction_clause,[],[f490])).
% 1.55/0.61  fof(f490,plain,(
% 1.55/0.61    $false | (spl4_3 | ~spl4_4)),
% 1.55/0.61    inference(subsumption_resolution,[],[f486,f120])).
% 1.55/0.61  fof(f120,plain,(
% 1.55/0.61    r2_hidden(sK1,sK2) | ~spl4_4),
% 1.55/0.61    inference(avatar_component_clause,[],[f119])).
% 1.55/0.61  fof(f119,plain,(
% 1.55/0.61    spl4_4 <=> r2_hidden(sK1,sK2)),
% 1.55/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.55/0.61  fof(f486,plain,(
% 1.55/0.61    ~r2_hidden(sK1,sK2) | spl4_3),
% 1.55/0.61    inference(resolution,[],[f475,f98])).
% 1.55/0.61  fof(f98,plain,(
% 1.55/0.61    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.55/0.61    inference(definition_unfolding,[],[f63,f88])).
% 1.55/0.61  fof(f88,plain,(
% 1.55/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.55/0.61    inference(definition_unfolding,[],[f64,f87])).
% 1.55/0.61  fof(f87,plain,(
% 1.55/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.55/0.61    inference(definition_unfolding,[],[f66,f80])).
% 1.55/0.61  fof(f80,plain,(
% 1.55/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f10])).
% 1.55/0.61  fof(f10,axiom,(
% 1.55/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.55/0.61  fof(f66,plain,(
% 1.55/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f9])).
% 1.55/0.61  fof(f9,axiom,(
% 1.55/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.55/0.61  fof(f64,plain,(
% 1.55/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.55/0.61    inference(cnf_transformation,[],[f12])).
% 1.55/0.61  fof(f12,axiom,(
% 1.55/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.55/0.61  fof(f63,plain,(
% 1.55/0.61    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.55/0.61    inference(cnf_transformation,[],[f6])).
% 1.55/0.61  fof(f6,axiom,(
% 1.55/0.61    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.55/0.61  fof(f475,plain,(
% 1.55/0.61    ( ! [X0] : (~r1_tarski(X0,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2)))) | ~r2_hidden(sK1,X0)) ) | spl4_3),
% 1.55/0.61    inference(resolution,[],[f117,f74])).
% 1.55/0.61  fof(f74,plain,(
% 1.55/0.61    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f49])).
% 1.55/0.61  fof(f49,plain,(
% 1.55/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.55/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).
% 1.55/0.61  fof(f48,plain,(
% 1.55/0.61    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.55/0.61    introduced(choice_axiom,[])).
% 1.55/0.61  fof(f47,plain,(
% 1.55/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.55/0.61    inference(rectify,[],[f46])).
% 1.55/0.61  fof(f46,plain,(
% 1.55/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.55/0.61    inference(nnf_transformation,[],[f31])).
% 1.55/0.61  fof(f31,plain,(
% 1.55/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.55/0.61    inference(ennf_transformation,[],[f1])).
% 1.55/0.61  fof(f1,axiom,(
% 1.55/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.55/0.61  fof(f117,plain,(
% 1.55/0.61    ~r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2)))) | spl4_3),
% 1.55/0.61    inference(avatar_component_clause,[],[f115])).
% 1.55/0.61  fof(f115,plain,(
% 1.55/0.61    spl4_3 <=> r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2))))),
% 1.55/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.55/0.61  fof(f465,plain,(
% 1.55/0.61    spl4_4 | ~spl4_7),
% 1.55/0.61    inference(avatar_split_clause,[],[f462,f270,f119])).
% 1.55/0.61  fof(f270,plain,(
% 1.55/0.61    spl4_7 <=> sP0(k2_enumset1(sK2,sK2,sK2,sK2),sK1,sK2)),
% 1.55/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.55/0.61  fof(f462,plain,(
% 1.55/0.61    r2_hidden(sK1,sK2) | ~spl4_7),
% 1.55/0.61    inference(resolution,[],[f272,f83])).
% 1.55/0.61  fof(f83,plain,(
% 1.55/0.61    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X2)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f52])).
% 1.55/0.61  fof(f52,plain,(
% 1.55/0.61    ! [X0,X1,X2] : ((~r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2))),
% 1.55/0.61    inference(rectify,[],[f51])).
% 1.55/0.61  fof(f51,plain,(
% 1.55/0.61    ! [X1,X2,X0] : ((~r2_hidden(X2,X1) & r2_hidden(X2,X0)) | ~sP0(X1,X2,X0))),
% 1.55/0.61    inference(nnf_transformation,[],[f37])).
% 1.55/0.61  fof(f37,plain,(
% 1.55/0.61    ! [X1,X2,X0] : ((~r2_hidden(X2,X1) & r2_hidden(X2,X0)) | ~sP0(X1,X2,X0))),
% 1.55/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.55/0.61  fof(f272,plain,(
% 1.55/0.61    sP0(k2_enumset1(sK2,sK2,sK2,sK2),sK1,sK2) | ~spl4_7),
% 1.55/0.61    inference(avatar_component_clause,[],[f270])).
% 1.55/0.61  fof(f459,plain,(
% 1.55/0.61    spl4_2 | ~spl4_6),
% 1.55/0.61    inference(avatar_contradiction_clause,[],[f458])).
% 1.55/0.61  fof(f458,plain,(
% 1.55/0.61    $false | (spl4_2 | ~spl4_6)),
% 1.55/0.61    inference(subsumption_resolution,[],[f455,f102])).
% 1.55/0.61  fof(f102,plain,(
% 1.55/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.55/0.61    inference(equality_resolution,[],[f70])).
% 1.55/0.61  fof(f70,plain,(
% 1.55/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.55/0.61    inference(cnf_transformation,[],[f44])).
% 1.55/0.61  fof(f44,plain,(
% 1.55/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.55/0.61    inference(flattening,[],[f43])).
% 1.55/0.61  fof(f43,plain,(
% 1.55/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.55/0.61    inference(nnf_transformation,[],[f5])).
% 1.55/0.61  fof(f5,axiom,(
% 1.55/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.55/0.61  fof(f455,plain,(
% 1.55/0.61    ~r1_tarski(sK1,sK1) | (spl4_2 | ~spl4_6)),
% 1.55/0.61    inference(resolution,[],[f449,f454])).
% 1.55/0.61  fof(f454,plain,(
% 1.55/0.61    ~r1_tarski(sK2,sK1) | (spl4_2 | ~spl4_6)),
% 1.55/0.61    inference(subsumption_resolution,[],[f453,f112])).
% 1.55/0.61  fof(f112,plain,(
% 1.55/0.61    sK1 != sK2 | spl4_2),
% 1.55/0.61    inference(avatar_component_clause,[],[f110])).
% 1.55/0.61  fof(f110,plain,(
% 1.55/0.61    spl4_2 <=> sK1 = sK2),
% 1.55/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.55/0.61  fof(f453,plain,(
% 1.55/0.61    sK1 = sK2 | ~r1_tarski(sK2,sK1) | ~spl4_6),
% 1.55/0.61    inference(resolution,[],[f450,f71])).
% 1.55/0.61  fof(f71,plain,(
% 1.55/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f44])).
% 1.55/0.61  fof(f450,plain,(
% 1.55/0.61    r1_tarski(sK1,sK2) | ~spl4_6),
% 1.55/0.61    inference(resolution,[],[f268,f145])).
% 1.55/0.61  fof(f145,plain,(
% 1.55/0.61    ( ! [X2,X1] : (~r2_hidden(X2,k2_enumset1(X1,X1,X1,X1)) | r1_tarski(X2,X1)) )),
% 1.55/0.61    inference(superposition,[],[f68,f97])).
% 1.55/0.61  fof(f97,plain,(
% 1.55/0.61    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 1.55/0.61    inference(definition_unfolding,[],[f62,f88])).
% 1.55/0.61  fof(f62,plain,(
% 1.55/0.61    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.55/0.61    inference(cnf_transformation,[],[f26])).
% 1.55/0.61  fof(f26,plain,(
% 1.55/0.61    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.55/0.61    inference(rectify,[],[f2])).
% 1.55/0.61  fof(f2,axiom,(
% 1.55/0.61    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.55/0.61  fof(f68,plain,(
% 1.55/0.61    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f30])).
% 1.55/0.61  fof(f30,plain,(
% 1.55/0.61    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 1.55/0.61    inference(ennf_transformation,[],[f11])).
% 1.55/0.61  fof(f11,axiom,(
% 1.55/0.61    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 1.55/0.61  fof(f268,plain,(
% 1.55/0.61    r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) | ~spl4_6),
% 1.55/0.61    inference(avatar_component_clause,[],[f266])).
% 1.55/0.61  fof(f266,plain,(
% 1.55/0.61    spl4_6 <=> r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,sK2))),
% 1.55/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.55/0.61  fof(f449,plain,(
% 1.55/0.61    ( ! [X10] : (r1_tarski(sK2,X10) | ~r1_tarski(sK1,X10)) ) | ~spl4_6),
% 1.55/0.61    inference(resolution,[],[f268,f172])).
% 1.55/0.61  fof(f172,plain,(
% 1.55/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) | ~r1_tarski(X2,X1) | r1_tarski(X0,X1)) )),
% 1.55/0.61    inference(superposition,[],[f81,f96])).
% 1.55/0.61  fof(f96,plain,(
% 1.55/0.61    ( ! [X0] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 1.55/0.61    inference(definition_unfolding,[],[f61,f89])).
% 1.55/0.61  fof(f89,plain,(
% 1.55/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.55/0.61    inference(definition_unfolding,[],[f65,f87])).
% 1.55/0.61  fof(f65,plain,(
% 1.55/0.61    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f16])).
% 1.55/0.61  fof(f16,axiom,(
% 1.55/0.61    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.55/0.61  fof(f61,plain,(
% 1.55/0.61    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.55/0.61    inference(cnf_transformation,[],[f25])).
% 1.55/0.61  fof(f25,plain,(
% 1.55/0.61    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.55/0.61    inference(rectify,[],[f3])).
% 1.55/0.61  fof(f3,axiom,(
% 1.55/0.61    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.55/0.61  fof(f81,plain,(
% 1.55/0.61    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f34])).
% 1.55/0.61  fof(f34,plain,(
% 1.55/0.61    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 1.55/0.61    inference(flattening,[],[f33])).
% 1.55/0.61  fof(f33,plain,(
% 1.55/0.61    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 1.55/0.61    inference(ennf_transformation,[],[f19])).
% 1.55/0.61  fof(f19,axiom,(
% 1.55/0.61    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).
% 1.55/0.61  fof(f443,plain,(
% 1.55/0.61    spl4_5),
% 1.55/0.61    inference(avatar_contradiction_clause,[],[f442])).
% 1.55/0.61  fof(f442,plain,(
% 1.55/0.61    $false | spl4_5),
% 1.55/0.61    inference(subsumption_resolution,[],[f441,f102])).
% 1.55/0.61  fof(f441,plain,(
% 1.55/0.61    ~r1_tarski(sK2,sK2) | spl4_5),
% 1.55/0.61    inference(resolution,[],[f439,f79])).
% 1.55/0.61  fof(f79,plain,(
% 1.55/0.61    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f32])).
% 1.55/0.61  fof(f32,plain,(
% 1.55/0.61    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.55/0.61    inference(ennf_transformation,[],[f22])).
% 1.55/0.61  fof(f22,axiom,(
% 1.55/0.61    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.55/0.61  fof(f439,plain,(
% 1.55/0.61    r2_hidden(sK2,sK2) | spl4_5),
% 1.55/0.61    inference(duplicate_literal_removal,[],[f438])).
% 1.55/0.61  fof(f438,plain,(
% 1.55/0.61    r2_hidden(sK2,sK2) | r2_hidden(sK2,sK2) | spl4_5),
% 1.55/0.61    inference(resolution,[],[f215,f264])).
% 1.55/0.61  fof(f264,plain,(
% 1.55/0.61    ~r1_xboole_0(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) | spl4_5),
% 1.55/0.61    inference(avatar_component_clause,[],[f262])).
% 1.55/0.61  fof(f262,plain,(
% 1.55/0.61    spl4_5 <=> r1_xboole_0(sK2,k2_enumset1(sK2,sK2,sK2,sK2))),
% 1.55/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.55/0.61  fof(f215,plain,(
% 1.55/0.61    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_enumset1(X1,X1,X1,X2)) | r2_hidden(X2,X0) | r2_hidden(X1,X0)) )),
% 1.55/0.61    inference(trivial_inequality_removal,[],[f214])).
% 1.55/0.61  fof(f214,plain,(
% 1.55/0.61    ( ! [X2,X0,X1] : (X0 != X0 | r1_xboole_0(X0,k2_enumset1(X1,X1,X1,X2)) | r2_hidden(X2,X0) | r2_hidden(X1,X0)) )),
% 1.55/0.61    inference(superposition,[],[f73,f99])).
% 1.55/0.61  fof(f99,plain,(
% 1.55/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_enumset1(X0,X0,X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.55/0.61    inference(definition_unfolding,[],[f82,f87])).
% 1.55/0.61  fof(f82,plain,(
% 1.55/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f35])).
% 1.55/0.61  fof(f35,plain,(
% 1.55/0.61    ! [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2))),
% 1.55/0.61    inference(ennf_transformation,[],[f13])).
% 1.55/0.61  fof(f13,axiom,(
% 1.55/0.61    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 1.55/0.61  fof(f73,plain,(
% 1.55/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f45])).
% 1.55/0.61  fof(f45,plain,(
% 1.55/0.61    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.55/0.61    inference(nnf_transformation,[],[f7])).
% 1.55/0.61  fof(f7,axiom,(
% 1.55/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.55/0.61  fof(f273,plain,(
% 1.55/0.61    ~spl4_5 | spl4_6 | spl4_7 | ~spl4_3),
% 1.55/0.61    inference(avatar_split_clause,[],[f259,f115,f270,f266,f262])).
% 1.55/0.61  fof(f259,plain,(
% 1.55/0.61    sP0(k2_enumset1(sK2,sK2,sK2,sK2),sK1,sK2) | r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) | ~r1_xboole_0(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) | ~spl4_3),
% 1.55/0.61    inference(resolution,[],[f101,f116])).
% 1.55/0.61  fof(f116,plain,(
% 1.55/0.61    r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2)))) | ~spl4_3),
% 1.55/0.61    inference(avatar_component_clause,[],[f115])).
% 1.55/0.61  fof(f101,plain,(
% 1.55/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_tarski(k2_enumset1(X0,X0,X0,X1))) | sP0(X1,X2,X0) | r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 1.55/0.61    inference(definition_unfolding,[],[f85,f88])).
% 1.55/0.61  fof(f85,plain,(
% 1.55/0.61    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | sP0(X1,X2,X0) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f38])).
% 1.55/0.61  fof(f38,plain,(
% 1.55/0.61    ! [X0,X1,X2] : ((~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | sP0(X1,X2,X0) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 1.55/0.61    inference(definition_folding,[],[f36,f37])).
% 1.55/0.61  fof(f36,plain,(
% 1.55/0.61    ! [X0,X1,X2] : ((~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 1.55/0.61    inference(ennf_transformation,[],[f4])).
% 1.55/0.61  fof(f4,axiom,(
% 1.55/0.61    ! [X0,X1,X2] : ~(~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & ~(~r2_hidden(X2,X1) & r2_hidden(X2,X0)) & r2_hidden(X2,k2_xboole_0(X0,X1)) & r1_xboole_0(X0,X1))),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).
% 1.55/0.61  fof(f189,plain,(
% 1.55/0.61    spl4_1),
% 1.55/0.61    inference(avatar_contradiction_clause,[],[f186])).
% 1.55/0.61  fof(f186,plain,(
% 1.55/0.61    $false | spl4_1),
% 1.55/0.61    inference(subsumption_resolution,[],[f108,f95])).
% 1.55/0.61  fof(f95,plain,(
% 1.55/0.61    ( ! [X0] : (r2_hidden(X0,k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0))))) )),
% 1.55/0.61    inference(definition_unfolding,[],[f57,f91])).
% 1.55/0.61  fof(f91,plain,(
% 1.55/0.61    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0)))) )),
% 1.55/0.61    inference(definition_unfolding,[],[f60,f88,f90])).
% 1.55/0.61  fof(f90,plain,(
% 1.55/0.61    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.55/0.61    inference(definition_unfolding,[],[f59,f87])).
% 1.55/0.61  fof(f59,plain,(
% 1.55/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.55/0.61    inference(cnf_transformation,[],[f8])).
% 1.55/0.61  fof(f8,axiom,(
% 1.55/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.55/0.61  fof(f60,plain,(
% 1.55/0.61    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.55/0.61    inference(cnf_transformation,[],[f20])).
% 1.55/0.61  fof(f20,axiom,(
% 1.55/0.61    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.55/0.61  fof(f57,plain,(
% 1.55/0.61    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 1.55/0.61    inference(cnf_transformation,[],[f21])).
% 1.55/0.61  fof(f21,axiom,(
% 1.55/0.61    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 1.55/0.61  fof(f108,plain,(
% 1.55/0.61    ~r2_hidden(sK1,k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK1,sK1,sK1,sK1)))) | spl4_1),
% 1.55/0.61    inference(avatar_component_clause,[],[f106])).
% 1.55/0.61  fof(f106,plain,(
% 1.55/0.61    spl4_1 <=> r2_hidden(sK1,k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK1,sK1,sK1,sK1))))),
% 1.55/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.55/0.61  fof(f123,plain,(
% 1.55/0.61    spl4_3 | spl4_4 | spl4_2),
% 1.55/0.61    inference(avatar_split_clause,[],[f94,f110,f119,f115])).
% 1.55/0.61  fof(f94,plain,(
% 1.55/0.61    sK1 = sK2 | r2_hidden(sK1,sK2) | r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2))))),
% 1.55/0.61    inference(definition_unfolding,[],[f53,f91])).
% 1.55/0.61  fof(f53,plain,(
% 1.55/0.61    sK1 = sK2 | r2_hidden(sK1,sK2) | r2_hidden(sK1,k1_ordinal1(sK2))),
% 1.55/0.61    inference(cnf_transformation,[],[f42])).
% 1.55/0.61  fof(f42,plain,(
% 1.55/0.61    ((sK1 != sK2 & ~r2_hidden(sK1,sK2)) | ~r2_hidden(sK1,k1_ordinal1(sK2))) & (sK1 = sK2 | r2_hidden(sK1,sK2) | r2_hidden(sK1,k1_ordinal1(sK2)))),
% 1.55/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f40,f41])).
% 1.55/0.61  fof(f41,plain,(
% 1.55/0.61    ? [X0,X1] : (((X0 != X1 & ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))) & (X0 = X1 | r2_hidden(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) => (((sK1 != sK2 & ~r2_hidden(sK1,sK2)) | ~r2_hidden(sK1,k1_ordinal1(sK2))) & (sK1 = sK2 | r2_hidden(sK1,sK2) | r2_hidden(sK1,k1_ordinal1(sK2))))),
% 1.55/0.61    introduced(choice_axiom,[])).
% 1.55/0.61  fof(f40,plain,(
% 1.55/0.61    ? [X0,X1] : (((X0 != X1 & ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))) & (X0 = X1 | r2_hidden(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))))),
% 1.55/0.61    inference(flattening,[],[f39])).
% 1.55/0.61  fof(f39,plain,(
% 1.55/0.61    ? [X0,X1] : (((X0 != X1 & ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | r2_hidden(X0,k1_ordinal1(X1))))),
% 1.55/0.61    inference(nnf_transformation,[],[f27])).
% 1.55/0.61  fof(f27,plain,(
% 1.55/0.61    ? [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <~> (X0 = X1 | r2_hidden(X0,X1)))),
% 1.55/0.61    inference(ennf_transformation,[],[f24])).
% 1.55/0.61  fof(f24,negated_conjecture,(
% 1.55/0.61    ~! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 1.55/0.61    inference(negated_conjecture,[],[f23])).
% 1.55/0.61  fof(f23,conjecture,(
% 1.55/0.61    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 1.55/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 1.55/0.61  fof(f122,plain,(
% 1.55/0.61    ~spl4_3 | ~spl4_4),
% 1.55/0.61    inference(avatar_split_clause,[],[f93,f119,f115])).
% 1.55/0.61  fof(f93,plain,(
% 1.55/0.61    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2))))),
% 1.55/0.61    inference(definition_unfolding,[],[f54,f91])).
% 1.55/0.61  fof(f54,plain,(
% 1.55/0.61    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK1,k1_ordinal1(sK2))),
% 1.55/0.61    inference(cnf_transformation,[],[f42])).
% 1.55/0.61  fof(f113,plain,(
% 1.55/0.61    ~spl4_1 | ~spl4_2),
% 1.55/0.61    inference(avatar_split_clause,[],[f104,f110,f106])).
% 1.55/0.61  fof(f104,plain,(
% 1.55/0.61    sK1 != sK2 | ~r2_hidden(sK1,k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK1,sK1,sK1,sK1))))),
% 1.55/0.61    inference(inner_rewriting,[],[f92])).
% 1.55/0.61  fof(f92,plain,(
% 1.55/0.61    sK1 != sK2 | ~r2_hidden(sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK2,sK2,sK2,sK2))))),
% 1.55/0.61    inference(definition_unfolding,[],[f55,f91])).
% 1.55/0.61  fof(f55,plain,(
% 1.55/0.61    sK1 != sK2 | ~r2_hidden(sK1,k1_ordinal1(sK2))),
% 1.55/0.61    inference(cnf_transformation,[],[f42])).
% 1.55/0.61  % SZS output end Proof for theBenchmark
% 1.55/0.61  % (26311)------------------------------
% 1.55/0.61  % (26311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.61  % (26311)Termination reason: Refutation
% 1.55/0.61  
% 1.55/0.61  % (26311)Memory used [KB]: 6524
% 1.55/0.61  % (26311)Time elapsed: 0.194 s
% 1.55/0.61  % (26311)------------------------------
% 1.55/0.61  % (26311)------------------------------
% 1.55/0.61  % (26283)Success in time 0.25 s
%------------------------------------------------------------------------------
