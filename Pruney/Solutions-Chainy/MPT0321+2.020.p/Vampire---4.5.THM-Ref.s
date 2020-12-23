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
% DateTime   : Thu Dec  3 12:42:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 365 expanded)
%              Number of leaves         :   19 ( 111 expanded)
%              Depth                    :   13
%              Number of atoms          :  278 (1136 expanded)
%              Number of equality atoms :   69 ( 458 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f263,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f123,f131,f155,f165,f168,f175,f233,f256,f261])).

fof(f261,plain,
    ( spl7_7
    | spl7_3
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f260,f96,f78,f67,f86])).

fof(f86,plain,
    ( spl7_7
  <=> ! [X5] :
        ( ~ r2_hidden(X5,sK2)
        | r2_hidden(X5,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f67,plain,
    ( spl7_3
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f78,plain,
    ( spl7_6
  <=> ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f96,plain,
    ( spl7_10
  <=> ! [X6] :
        ( ~ r2_hidden(X6,sK3)
        | r2_hidden(X6,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f260,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X5,sK2)
        | r2_hidden(X5,sK0) )
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f173,f217])).

fof(f217,plain,
    ( sK1 = sK3
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f210,f190])).

fof(f190,plain,
    ( sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | ~ spl7_6 ),
    inference(resolution,[],[f182,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f182,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl7_6 ),
    inference(duplicate_literal_removal,[],[f181])).

fof(f181,plain,
    ( r1_tarski(sK1,sK3)
    | r1_tarski(sK1,sK3)
    | ~ spl7_6 ),
    inference(resolution,[],[f169,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f169,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(X0,sK3),sK1)
        | r1_tarski(X0,sK3) )
    | ~ spl7_6 ),
    inference(resolution,[],[f79,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f79,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f210,plain,
    ( sK3 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | ~ spl7_10 ),
    inference(superposition,[],[f192,f50])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f36,f37,f37])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f192,plain,
    ( sK3 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))
    | ~ spl7_10 ),
    inference(resolution,[],[f189,f51])).

fof(f189,plain,
    ( r1_tarski(sK3,sK1)
    | ~ spl7_10 ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,
    ( r1_tarski(sK3,sK1)
    | r1_tarski(sK3,sK1)
    | ~ spl7_10 ),
    inference(resolution,[],[f176,f39])).

fof(f176,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(X0,sK1),sK3)
        | r1_tarski(X0,sK1) )
    | ~ spl7_10 ),
    inference(resolution,[],[f97,f40])).

fof(f97,plain,
    ( ! [X6] :
        ( r2_hidden(X6,sK1)
        | ~ r2_hidden(X6,sK3) )
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f96])).

fof(f173,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,sK3)
      | ~ r2_hidden(X5,sK2)
      | r2_hidden(X5,sK0) ) ),
    inference(resolution,[],[f64,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f64,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X5,sK3)
      | ~ r2_hidden(X4,sK2) ) ),
    inference(superposition,[],[f49,f30])).

fof(f30,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( sK1 != sK3
      | sK0 != sK2 )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f17])).

fof(f17,plain,
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

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f256,plain,
    ( spl7_2
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | spl7_2
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f60,f217])).

fof(f60,plain,
    ( sK1 != sK3
    | spl7_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl7_2
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f233,plain,
    ( spl7_1
    | ~ spl7_4
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | spl7_1
    | ~ spl7_4
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f57,f206])).

fof(f206,plain,
    ( sK0 = sK2
    | ~ spl7_4
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f199,f186])).

fof(f186,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl7_4 ),
    inference(resolution,[],[f179,f51])).

fof(f179,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl7_4 ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,
    ( r1_tarski(sK0,sK2)
    | r1_tarski(sK0,sK2)
    | ~ spl7_4 ),
    inference(resolution,[],[f166,f39])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(X0,sK2),sK0)
        | r1_tarski(X0,sK2) )
    | ~ spl7_4 ),
    inference(resolution,[],[f71,f40])).

fof(f71,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl7_4
  <=> ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f199,plain,
    ( sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl7_7 ),
    inference(superposition,[],[f191,f50])).

fof(f191,plain,
    ( sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
    | ~ spl7_7 ),
    inference(resolution,[],[f185,f51])).

fof(f185,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl7_7 ),
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,
    ( r1_tarski(sK2,sK0)
    | r1_tarski(sK2,sK0)
    | ~ spl7_7 ),
    inference(resolution,[],[f170,f39])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(X0,sK0),sK2)
        | r1_tarski(X0,sK0) )
    | ~ spl7_7 ),
    inference(resolution,[],[f87,f40])).

fof(f87,plain,
    ( ! [X5] :
        ( r2_hidden(X5,sK0)
        | ~ r2_hidden(X5,sK2) )
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f57,plain,
    ( sK0 != sK2
    | spl7_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl7_1
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f175,plain,
    ( spl7_9
    | spl7_10 ),
    inference(avatar_split_clause,[],[f174,f96,f93])).

fof(f93,plain,
    ( spl7_9
  <=> ! [X7] : ~ r2_hidden(X7,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f174,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,sK3)
      | ~ r2_hidden(X7,sK2)
      | r2_hidden(X6,sK1) ) ),
    inference(resolution,[],[f64,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f168,plain,
    ( spl7_5
    | spl7_6 ),
    inference(avatar_split_clause,[],[f167,f78,f75])).

fof(f75,plain,
    ( spl7_5
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f167,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK3)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f63,f49])).

fof(f63,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X3,sK3) ) ),
    inference(superposition,[],[f48,f30])).

fof(f165,plain,
    ( spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f164,f70,f67])).

fof(f164,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK2)
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f62,f49])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X0,sK2) ) ),
    inference(superposition,[],[f47,f30])).

fof(f155,plain,
    ( spl7_5
    | spl7_3
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f152,f93,f67,f75])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl7_9 ),
    inference(resolution,[],[f137,f145])).

fof(f145,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_xboole_0,sK3))
    | ~ spl7_9 ),
    inference(forward_demodulation,[],[f111,f134])).

fof(f134,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl7_9 ),
    inference(forward_demodulation,[],[f30,f112])).

fof(f112,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_9 ),
    inference(resolution,[],[f94,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f94,plain,
    ( ! [X7] : ~ r2_hidden(X7,sK2)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f93])).

fof(f111,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f62,f94])).

fof(f137,plain,
    ( ! [X4,X5] :
        ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(k1_xboole_0,sK3))
        | ~ r2_hidden(X5,sK1)
        | ~ r2_hidden(X4,sK0) )
    | ~ spl7_9 ),
    inference(superposition,[],[f49,f134])).

fof(f131,plain,(
    ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f31,f105])).

fof(f105,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_5 ),
    inference(resolution,[],[f76,f35])).

fof(f76,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f31,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f123,plain,(
    ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f32,f99])).

fof(f99,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_3 ),
    inference(resolution,[],[f68,f35])).

fof(f68,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f32,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f33,f59,f56])).

fof(f33,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:55:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (23362)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (23377)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.52  % (23369)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.52  % (23350)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (23352)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (23347)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (23348)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (23347)Refutation not found, incomplete strategy% (23347)------------------------------
% 0.22/0.53  % (23347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (23347)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (23347)Memory used [KB]: 1663
% 0.22/0.53  % (23347)Time elapsed: 0.115 s
% 0.22/0.53  % (23347)------------------------------
% 0.22/0.53  % (23347)------------------------------
% 0.22/0.53  % (23349)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (23375)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (23353)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (23355)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (23363)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (23359)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (23371)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (23374)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (23364)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (23376)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (23365)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (23367)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (23349)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (23372)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (23361)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (23359)Refutation not found, incomplete strategy% (23359)------------------------------
% 0.22/0.55  % (23359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23360)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (23366)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.46/0.55  % (23358)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.46/0.55  % (23370)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.46/0.55  % (23368)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.46/0.55  % (23359)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (23359)Memory used [KB]: 10618
% 1.46/0.55  % (23359)Time elapsed: 0.093 s
% 1.46/0.55  % (23359)------------------------------
% 1.46/0.55  % (23359)------------------------------
% 1.46/0.55  % (23354)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.46/0.55  % SZS output start Proof for theBenchmark
% 1.46/0.55  fof(f263,plain,(
% 1.46/0.55    $false),
% 1.46/0.55    inference(avatar_sat_refutation,[],[f61,f123,f131,f155,f165,f168,f175,f233,f256,f261])).
% 1.46/0.55  fof(f261,plain,(
% 1.46/0.55    spl7_7 | spl7_3 | ~spl7_6 | ~spl7_10),
% 1.46/0.55    inference(avatar_split_clause,[],[f260,f96,f78,f67,f86])).
% 1.46/0.55  fof(f86,plain,(
% 1.46/0.55    spl7_7 <=> ! [X5] : (~r2_hidden(X5,sK2) | r2_hidden(X5,sK0))),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.46/0.55  fof(f67,plain,(
% 1.46/0.55    spl7_3 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.46/0.55  fof(f78,plain,(
% 1.46/0.55    spl7_6 <=> ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1))),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.46/0.55  fof(f96,plain,(
% 1.46/0.55    spl7_10 <=> ! [X6] : (~r2_hidden(X6,sK3) | r2_hidden(X6,sK1))),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.46/0.55  fof(f260,plain,(
% 1.46/0.55    ( ! [X4,X5] : (~r2_hidden(X4,sK1) | ~r2_hidden(X5,sK2) | r2_hidden(X5,sK0)) ) | (~spl7_6 | ~spl7_10)),
% 1.46/0.55    inference(forward_demodulation,[],[f173,f217])).
% 1.46/0.55  fof(f217,plain,(
% 1.46/0.55    sK1 = sK3 | (~spl7_6 | ~spl7_10)),
% 1.46/0.55    inference(forward_demodulation,[],[f210,f190])).
% 1.46/0.55  fof(f190,plain,(
% 1.46/0.55    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) | ~spl7_6),
% 1.46/0.55    inference(resolution,[],[f182,f51])).
% 1.46/0.55  fof(f51,plain,(
% 1.46/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.46/0.55    inference(definition_unfolding,[],[f38,f37])).
% 1.46/0.55  fof(f37,plain,(
% 1.46/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.46/0.55    inference(cnf_transformation,[],[f7])).
% 1.46/0.55  fof(f7,axiom,(
% 1.46/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.46/0.55  fof(f38,plain,(
% 1.46/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f15])).
% 1.46/0.55  fof(f15,plain,(
% 1.46/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.46/0.55    inference(ennf_transformation,[],[f5])).
% 1.46/0.55  fof(f5,axiom,(
% 1.46/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.46/0.55  fof(f182,plain,(
% 1.46/0.55    r1_tarski(sK1,sK3) | ~spl7_6),
% 1.46/0.55    inference(duplicate_literal_removal,[],[f181])).
% 1.46/0.55  fof(f181,plain,(
% 1.46/0.55    r1_tarski(sK1,sK3) | r1_tarski(sK1,sK3) | ~spl7_6),
% 1.46/0.55    inference(resolution,[],[f169,f39])).
% 1.46/0.55  fof(f39,plain,(
% 1.46/0.55    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f22])).
% 1.46/0.55  fof(f22,plain,(
% 1.46/0.55    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.46/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f21])).
% 1.46/0.55  fof(f21,plain,(
% 1.46/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.46/0.55    introduced(choice_axiom,[])).
% 1.46/0.55  fof(f16,plain,(
% 1.46/0.55    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.46/0.55    inference(ennf_transformation,[],[f11])).
% 1.46/0.55  fof(f11,plain,(
% 1.46/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.46/0.55    inference(unused_predicate_definition_removal,[],[f2])).
% 1.46/0.55  fof(f2,axiom,(
% 1.46/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.46/0.55  fof(f169,plain,(
% 1.46/0.55    ( ! [X0] : (~r2_hidden(sK5(X0,sK3),sK1) | r1_tarski(X0,sK3)) ) | ~spl7_6),
% 1.46/0.55    inference(resolution,[],[f79,f40])).
% 1.46/0.55  fof(f40,plain,(
% 1.46/0.55    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f22])).
% 1.46/0.55  fof(f79,plain,(
% 1.46/0.55    ( ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1)) ) | ~spl7_6),
% 1.46/0.55    inference(avatar_component_clause,[],[f78])).
% 1.46/0.55  fof(f210,plain,(
% 1.46/0.55    sK3 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) | ~spl7_10),
% 1.46/0.55    inference(superposition,[],[f192,f50])).
% 1.46/0.55  fof(f50,plain,(
% 1.46/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.46/0.55    inference(definition_unfolding,[],[f36,f37,f37])).
% 1.46/0.55  fof(f36,plain,(
% 1.46/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f1])).
% 1.46/0.55  fof(f1,axiom,(
% 1.46/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.46/0.55  fof(f192,plain,(
% 1.46/0.55    sK3 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) | ~spl7_10),
% 1.46/0.55    inference(resolution,[],[f189,f51])).
% 1.46/0.55  fof(f189,plain,(
% 1.46/0.55    r1_tarski(sK3,sK1) | ~spl7_10),
% 1.46/0.55    inference(duplicate_literal_removal,[],[f188])).
% 1.46/0.55  fof(f188,plain,(
% 1.46/0.55    r1_tarski(sK3,sK1) | r1_tarski(sK3,sK1) | ~spl7_10),
% 1.46/0.55    inference(resolution,[],[f176,f39])).
% 1.46/0.55  fof(f176,plain,(
% 1.46/0.55    ( ! [X0] : (~r2_hidden(sK5(X0,sK1),sK3) | r1_tarski(X0,sK1)) ) | ~spl7_10),
% 1.46/0.55    inference(resolution,[],[f97,f40])).
% 1.46/0.55  fof(f97,plain,(
% 1.46/0.55    ( ! [X6] : (r2_hidden(X6,sK1) | ~r2_hidden(X6,sK3)) ) | ~spl7_10),
% 1.46/0.55    inference(avatar_component_clause,[],[f96])).
% 1.46/0.55  fof(f173,plain,(
% 1.46/0.55    ( ! [X4,X5] : (~r2_hidden(X4,sK3) | ~r2_hidden(X5,sK2) | r2_hidden(X5,sK0)) )),
% 1.46/0.55    inference(resolution,[],[f64,f47])).
% 1.46/0.55  fof(f47,plain,(
% 1.46/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f29])).
% 1.46/0.55  fof(f29,plain,(
% 1.46/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.46/0.55    inference(flattening,[],[f28])).
% 1.46/0.55  fof(f28,plain,(
% 1.46/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.46/0.55    inference(nnf_transformation,[],[f8])).
% 1.46/0.55  fof(f8,axiom,(
% 1.46/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.46/0.55  fof(f64,plain,(
% 1.46/0.55    ( ! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X5,sK3) | ~r2_hidden(X4,sK2)) )),
% 1.46/0.55    inference(superposition,[],[f49,f30])).
% 1.46/0.55  fof(f30,plain,(
% 1.46/0.55    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 1.46/0.55    inference(cnf_transformation,[],[f18])).
% 1.46/0.56  fof(f18,plain,(
% 1.46/0.56    (sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 1.46/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f17])).
% 1.46/0.56  fof(f17,plain,(
% 1.46/0.56    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)) => ((sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f13,plain,(
% 1.46/0.56    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 1.46/0.56    inference(flattening,[],[f12])).
% 1.46/0.56  fof(f12,plain,(
% 1.46/0.56    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 1.46/0.56    inference(ennf_transformation,[],[f10])).
% 1.46/0.56  fof(f10,negated_conjecture,(
% 1.46/0.56    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.46/0.56    inference(negated_conjecture,[],[f9])).
% 1.46/0.56  fof(f9,conjecture,(
% 1.46/0.56    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 1.46/0.56  fof(f49,plain,(
% 1.46/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f29])).
% 1.46/0.56  fof(f256,plain,(
% 1.46/0.56    spl7_2 | ~spl7_6 | ~spl7_10),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f245])).
% 1.46/0.56  fof(f245,plain,(
% 1.46/0.56    $false | (spl7_2 | ~spl7_6 | ~spl7_10)),
% 1.46/0.56    inference(subsumption_resolution,[],[f60,f217])).
% 1.46/0.56  fof(f60,plain,(
% 1.46/0.56    sK1 != sK3 | spl7_2),
% 1.46/0.56    inference(avatar_component_clause,[],[f59])).
% 1.46/0.56  fof(f59,plain,(
% 1.46/0.56    spl7_2 <=> sK1 = sK3),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.46/0.56  fof(f233,plain,(
% 1.46/0.56    spl7_1 | ~spl7_4 | ~spl7_7),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f221])).
% 1.46/0.56  fof(f221,plain,(
% 1.46/0.56    $false | (spl7_1 | ~spl7_4 | ~spl7_7)),
% 1.46/0.56    inference(subsumption_resolution,[],[f57,f206])).
% 1.46/0.56  fof(f206,plain,(
% 1.46/0.56    sK0 = sK2 | (~spl7_4 | ~spl7_7)),
% 1.46/0.56    inference(forward_demodulation,[],[f199,f186])).
% 1.46/0.56  fof(f186,plain,(
% 1.46/0.56    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl7_4),
% 1.46/0.56    inference(resolution,[],[f179,f51])).
% 1.46/0.56  fof(f179,plain,(
% 1.46/0.56    r1_tarski(sK0,sK2) | ~spl7_4),
% 1.46/0.56    inference(duplicate_literal_removal,[],[f178])).
% 1.46/0.56  fof(f178,plain,(
% 1.46/0.56    r1_tarski(sK0,sK2) | r1_tarski(sK0,sK2) | ~spl7_4),
% 1.46/0.56    inference(resolution,[],[f166,f39])).
% 1.46/0.56  fof(f166,plain,(
% 1.46/0.56    ( ! [X0] : (~r2_hidden(sK5(X0,sK2),sK0) | r1_tarski(X0,sK2)) ) | ~spl7_4),
% 1.46/0.56    inference(resolution,[],[f71,f40])).
% 1.46/0.56  fof(f71,plain,(
% 1.46/0.56    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0)) ) | ~spl7_4),
% 1.46/0.56    inference(avatar_component_clause,[],[f70])).
% 1.46/0.56  fof(f70,plain,(
% 1.46/0.56    spl7_4 <=> ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.46/0.56  fof(f199,plain,(
% 1.46/0.56    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl7_7),
% 1.46/0.56    inference(superposition,[],[f191,f50])).
% 1.46/0.56  fof(f191,plain,(
% 1.46/0.56    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) | ~spl7_7),
% 1.46/0.56    inference(resolution,[],[f185,f51])).
% 1.46/0.56  fof(f185,plain,(
% 1.46/0.56    r1_tarski(sK2,sK0) | ~spl7_7),
% 1.46/0.56    inference(duplicate_literal_removal,[],[f184])).
% 1.46/0.56  fof(f184,plain,(
% 1.46/0.56    r1_tarski(sK2,sK0) | r1_tarski(sK2,sK0) | ~spl7_7),
% 1.46/0.56    inference(resolution,[],[f170,f39])).
% 1.46/0.56  fof(f170,plain,(
% 1.46/0.56    ( ! [X0] : (~r2_hidden(sK5(X0,sK0),sK2) | r1_tarski(X0,sK0)) ) | ~spl7_7),
% 1.46/0.56    inference(resolution,[],[f87,f40])).
% 1.46/0.56  fof(f87,plain,(
% 1.46/0.56    ( ! [X5] : (r2_hidden(X5,sK0) | ~r2_hidden(X5,sK2)) ) | ~spl7_7),
% 1.46/0.56    inference(avatar_component_clause,[],[f86])).
% 1.46/0.56  fof(f57,plain,(
% 1.46/0.56    sK0 != sK2 | spl7_1),
% 1.46/0.56    inference(avatar_component_clause,[],[f56])).
% 1.46/0.56  fof(f56,plain,(
% 1.46/0.56    spl7_1 <=> sK0 = sK2),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.46/0.56  fof(f175,plain,(
% 1.46/0.56    spl7_9 | spl7_10),
% 1.46/0.56    inference(avatar_split_clause,[],[f174,f96,f93])).
% 1.46/0.56  fof(f93,plain,(
% 1.46/0.56    spl7_9 <=> ! [X7] : ~r2_hidden(X7,sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.46/0.56  fof(f174,plain,(
% 1.46/0.56    ( ! [X6,X7] : (~r2_hidden(X6,sK3) | ~r2_hidden(X7,sK2) | r2_hidden(X6,sK1)) )),
% 1.46/0.56    inference(resolution,[],[f64,f48])).
% 1.46/0.56  fof(f48,plain,(
% 1.46/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f29])).
% 1.46/0.56  fof(f168,plain,(
% 1.46/0.56    spl7_5 | spl7_6),
% 1.46/0.56    inference(avatar_split_clause,[],[f167,f78,f75])).
% 1.46/0.56  fof(f75,plain,(
% 1.46/0.56    spl7_5 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.46/0.56  fof(f167,plain,(
% 1.46/0.56    ( ! [X0,X1] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0)) )),
% 1.46/0.56    inference(resolution,[],[f63,f49])).
% 1.46/0.56  fof(f63,plain,(
% 1.46/0.56    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X3,sK3)) )),
% 1.46/0.56    inference(superposition,[],[f48,f30])).
% 1.46/0.56  fof(f165,plain,(
% 1.46/0.56    spl7_3 | spl7_4),
% 1.46/0.56    inference(avatar_split_clause,[],[f164,f70,f67])).
% 1.46/0.56  fof(f164,plain,(
% 1.46/0.56    ( ! [X0,X1] : (r2_hidden(X0,sK2) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) )),
% 1.46/0.56    inference(resolution,[],[f62,f49])).
% 1.46/0.56  fof(f62,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X0,sK2)) )),
% 1.46/0.56    inference(superposition,[],[f47,f30])).
% 1.46/0.56  fof(f155,plain,(
% 1.46/0.56    spl7_5 | spl7_3 | ~spl7_9),
% 1.46/0.56    inference(avatar_split_clause,[],[f152,f93,f67,f75])).
% 1.46/0.56  fof(f152,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0)) ) | ~spl7_9),
% 1.46/0.56    inference(resolution,[],[f137,f145])).
% 1.46/0.56  fof(f145,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_xboole_0,sK3))) ) | ~spl7_9),
% 1.46/0.56    inference(forward_demodulation,[],[f111,f134])).
% 1.46/0.56  fof(f134,plain,(
% 1.46/0.56    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,sK3) | ~spl7_9),
% 1.46/0.56    inference(forward_demodulation,[],[f30,f112])).
% 1.46/0.56  fof(f112,plain,(
% 1.46/0.56    k1_xboole_0 = sK2 | ~spl7_9),
% 1.46/0.56    inference(resolution,[],[f94,f35])).
% 1.46/0.56  fof(f35,plain,(
% 1.46/0.56    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.46/0.56    inference(cnf_transformation,[],[f20])).
% 1.46/0.56  fof(f20,plain,(
% 1.46/0.56    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 1.46/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f19])).
% 1.46/0.56  fof(f19,plain,(
% 1.46/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f14,plain,(
% 1.46/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.46/0.56    inference(ennf_transformation,[],[f4])).
% 1.46/0.56  fof(f4,axiom,(
% 1.46/0.56    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.46/0.56  fof(f94,plain,(
% 1.46/0.56    ( ! [X7] : (~r2_hidden(X7,sK2)) ) | ~spl7_9),
% 1.46/0.56    inference(avatar_component_clause,[],[f93])).
% 1.46/0.56  fof(f111,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))) ) | ~spl7_9),
% 1.46/0.56    inference(subsumption_resolution,[],[f62,f94])).
% 1.46/0.56  fof(f137,plain,(
% 1.46/0.56    ( ! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(k1_xboole_0,sK3)) | ~r2_hidden(X5,sK1) | ~r2_hidden(X4,sK0)) ) | ~spl7_9),
% 1.46/0.56    inference(superposition,[],[f49,f134])).
% 1.46/0.56  fof(f131,plain,(
% 1.46/0.56    ~spl7_5),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f127])).
% 1.46/0.56  fof(f127,plain,(
% 1.46/0.56    $false | ~spl7_5),
% 1.46/0.56    inference(subsumption_resolution,[],[f31,f105])).
% 1.46/0.56  fof(f105,plain,(
% 1.46/0.56    k1_xboole_0 = sK0 | ~spl7_5),
% 1.46/0.56    inference(resolution,[],[f76,f35])).
% 1.46/0.56  fof(f76,plain,(
% 1.46/0.56    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl7_5),
% 1.46/0.56    inference(avatar_component_clause,[],[f75])).
% 1.46/0.56  fof(f31,plain,(
% 1.46/0.56    k1_xboole_0 != sK0),
% 1.46/0.56    inference(cnf_transformation,[],[f18])).
% 1.46/0.56  fof(f123,plain,(
% 1.46/0.56    ~spl7_3),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f118])).
% 1.46/0.56  fof(f118,plain,(
% 1.46/0.56    $false | ~spl7_3),
% 1.46/0.56    inference(subsumption_resolution,[],[f32,f99])).
% 1.46/0.56  fof(f99,plain,(
% 1.46/0.56    k1_xboole_0 = sK1 | ~spl7_3),
% 1.46/0.56    inference(resolution,[],[f68,f35])).
% 1.46/0.56  fof(f68,plain,(
% 1.46/0.56    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl7_3),
% 1.46/0.56    inference(avatar_component_clause,[],[f67])).
% 1.46/0.56  fof(f32,plain,(
% 1.46/0.56    k1_xboole_0 != sK1),
% 1.46/0.56    inference(cnf_transformation,[],[f18])).
% 1.46/0.56  fof(f61,plain,(
% 1.46/0.56    ~spl7_1 | ~spl7_2),
% 1.46/0.56    inference(avatar_split_clause,[],[f33,f59,f56])).
% 1.46/0.56  fof(f33,plain,(
% 1.46/0.56    sK1 != sK3 | sK0 != sK2),
% 1.46/0.56    inference(cnf_transformation,[],[f18])).
% 1.46/0.56  % SZS output end Proof for theBenchmark
% 1.46/0.56  % (23349)------------------------------
% 1.46/0.56  % (23349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (23349)Termination reason: Refutation
% 1.46/0.56  
% 1.46/0.56  % (23349)Memory used [KB]: 10746
% 1.46/0.56  % (23349)Time elapsed: 0.108 s
% 1.46/0.56  % (23349)------------------------------
% 1.46/0.56  % (23349)------------------------------
% 1.46/0.56  % (23346)Success in time 0.191 s
%------------------------------------------------------------------------------
