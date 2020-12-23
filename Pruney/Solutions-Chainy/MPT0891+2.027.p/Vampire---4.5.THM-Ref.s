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
% DateTime   : Thu Dec  3 12:59:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 303 expanded)
%              Number of leaves         :   24 ( 106 expanded)
%              Depth                    :   13
%              Number of atoms          :  319 ( 785 expanded)
%              Number of equality atoms :  155 ( 442 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f427,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f230,f241,f248,f254,f258,f291,f319,f330,f336,f379,f383,f426])).

fof(f426,plain,
    ( ~ spl7_9
    | spl7_10 ),
    inference(avatar_contradiction_clause,[],[f401])).

fof(f401,plain,
    ( $false
    | ~ spl7_9
    | spl7_10 ),
    inference(unit_resulting_resolution,[],[f285,f127,f235,f112])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(X1,X2),X3) != X0
      | ~ r2_hidden(X1,k1_tarski(X0))
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(X1,X2),X3) != X0
      | ~ r2_hidden(X1,k1_tarski(X0))
      | k1_xboole_0 = k1_tarski(X0)
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(superposition,[],[f50,f97])).

fof(f97,plain,(
    ! [X1] :
      ( sK5(k1_tarski(X1)) = X1
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(resolution,[],[f95,f28])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f95,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X2))
      | X1 = X2 ) ),
    inference(condensation,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(X1))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f93,f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_enumset1(X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f41,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_enumset1(X0,X0,X1))
      | ~ r2_hidden(X1,k1_tarski(X2)) ) ),
    inference(trivial_inequality_removal,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k1_enumset1(X0,X0,X1) != k1_enumset1(X0,X0,X1)
      | ~ r2_hidden(X1,k1_tarski(X2))
      | r2_hidden(X2,k1_enumset1(X0,X0,X1)) ) ),
    inference(superposition,[],[f58,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_enumset1(X0,X0,X1) != k4_xboole_0(k1_enumset1(X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f45,f30,f30])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f50,plain,(
    ! [X4,X2,X0,X3] :
      ( sK5(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f26,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f26,plain,(
    ! [X4,X2,X0,X3] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X2,X0)
      | k3_mcart_1(X2,X3,X4) != sK5(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f235,plain,
    ( sK3 = k4_tarski(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl7_9
  <=> sK3 = k4_tarski(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f127,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(condensation,[],[f124])).

fof(f124,plain,(
    ! [X8,X9] :
      ( r2_hidden(X8,k1_tarski(X9))
      | r2_hidden(X9,k1_tarski(X9)) ) ),
    inference(resolution,[],[f120,f66])).

fof(f66,plain,(
    ! [X3,X1] : r2_hidden(X3,k1_enumset1(X3,X3,X1)) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k1_enumset1(X3,X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f42,f30])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f120,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X8,k1_enumset1(X6,X6,X7))
      | r2_hidden(X7,k1_tarski(X8))
      | r2_hidden(X6,k1_tarski(X8)) ) ),
    inference(trivial_inequality_removal,[],[f119])).

fof(f119,plain,(
    ! [X6,X8,X7] :
      ( k1_enumset1(X6,X6,X7) != k1_enumset1(X6,X6,X7)
      | ~ r2_hidden(X8,k1_enumset1(X6,X6,X7))
      | r2_hidden(X7,k1_tarski(X8))
      | r2_hidden(X6,k1_tarski(X8)) ) ),
    inference(superposition,[],[f35,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_enumset1(X0,X0,X1) = k4_xboole_0(k1_enumset1(X0,X0,X1),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f46,f30,f30])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X1,X2)
      | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f285,plain,
    ( k1_xboole_0 != k1_tarski(sK3)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl7_10
  <=> k1_xboole_0 = k1_tarski(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f383,plain,
    ( spl7_4
    | ~ spl7_5
    | spl7_6
    | spl7_7
    | spl7_9
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f382,f77,f233,f221,f217,f213,f209])).

fof(f209,plain,
    ( spl7_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f213,plain,
    ( spl7_5
  <=> m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f217,plain,
    ( spl7_6
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f221,plain,
    ( spl7_7
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f77,plain,
    ( spl7_3
  <=> sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f382,plain,
    ( sK3 = k4_tarski(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0
    | ~ spl7_3 ),
    inference(superposition,[],[f60,f79])).

fof(f79,plain,
    ( sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f47,f37,f36])).

fof(f37,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f379,plain,
    ( spl7_10
    | ~ spl7_15 ),
    inference(avatar_contradiction_clause,[],[f354])).

fof(f354,plain,
    ( $false
    | spl7_10
    | ~ spl7_15 ),
    inference(unit_resulting_resolution,[],[f285,f127,f335,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | ~ r2_hidden(X2,k1_tarski(X0))
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | ~ r2_hidden(X2,k1_tarski(X0))
      | k1_xboole_0 = k1_tarski(X0)
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(superposition,[],[f24,f96])).

fof(f96,plain,(
    ! [X0] :
      ( sK4(k1_tarski(X0)) = X0
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(resolution,[],[f95,f25])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f24,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK4(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f335,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),sK3)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f333])).

fof(f333,plain,
    ( spl7_15
  <=> sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f336,plain,
    ( spl7_4
    | ~ spl7_5
    | spl7_6
    | spl7_7
    | spl7_15
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f331,f69,f333,f221,f217,f213,f209])).

fof(f69,plain,
    ( spl7_1
  <=> sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f331,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),sK3)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0
    | ~ spl7_1 ),
    inference(superposition,[],[f60,f71])).

fof(f71,plain,
    ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f330,plain,(
    ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f81,f326])).

fof(f326,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl7_10 ),
    inference(superposition,[],[f127,f286])).

fof(f286,plain,
    ( k1_xboole_0 = k1_tarski(sK3)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f284])).

fof(f81,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f29,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f29,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f319,plain,(
    spl7_11 ),
    inference(avatar_contradiction_clause,[],[f311])).

fof(f311,plain,
    ( $false
    | spl7_11 ),
    inference(unit_resulting_resolution,[],[f290,f66,f290,f120])).

fof(f290,plain,
    ( ~ r2_hidden(sK3,k1_tarski(sK3))
    | spl7_11 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl7_11
  <=> r2_hidden(sK3,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f291,plain,
    ( spl7_10
    | ~ spl7_11
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f263,f225,f288,f284])).

fof(f225,plain,
    ( spl7_8
  <=> sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f263,plain,
    ( ~ r2_hidden(sK3,k1_tarski(sK3))
    | k1_xboole_0 = k1_tarski(sK3)
    | ~ spl7_8 ),
    inference(superposition,[],[f130,f227])).

fof(f227,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f225])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(k4_tarski(k4_tarski(X1,X0),X2)))
      | k1_xboole_0 = k1_tarski(k4_tarski(k4_tarski(X1,X0),X2)) ) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X6,X4,X7,X5] :
      ( k4_tarski(k4_tarski(X5,X6),X7) != X4
      | ~ r2_hidden(X6,k1_tarski(X4))
      | k1_xboole_0 = k1_tarski(X4) ) ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,(
    ! [X6,X4,X7,X5] :
      ( k4_tarski(k4_tarski(X5,X6),X7) != X4
      | ~ r2_hidden(X6,k1_tarski(X4))
      | k1_xboole_0 = k1_tarski(X4)
      | k1_xboole_0 = k1_tarski(X4) ) ),
    inference(superposition,[],[f49,f97])).

fof(f49,plain,(
    ! [X4,X2,X0,X3] :
      ( sK5(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f27,f36])).

fof(f27,plain,(
    ! [X4,X2,X0,X3] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X3,X0)
      | k3_mcart_1(X2,X3,X4) != sK5(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f258,plain,
    ( spl7_4
    | ~ spl7_5
    | spl7_6
    | spl7_7
    | spl7_8
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f257,f73,f225,f221,f217,f213,f209])).

fof(f73,plain,
    ( spl7_2
  <=> sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f257,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0
    | ~ spl7_2 ),
    inference(superposition,[],[f60,f75])).

fof(f75,plain,
    ( sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f254,plain,(
    ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f21,f223])).

fof(f223,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f221])).

fof(f21,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) != X3
                & k6_mcart_1(X0,X1,X2,X3) != X3
                & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).

fof(f248,plain,(
    ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f22,f219])).

fof(f219,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f217])).

fof(f22,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f241,plain,(
    ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f20,f211])).

fof(f211,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f209])).

fof(f20,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).

fof(f230,plain,(
    spl7_5 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | spl7_5 ),
    inference(subsumption_resolution,[],[f48,f215])).

fof(f215,plain,
    ( ~ m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f213])).

fof(f48,plain,(
    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f19,f37])).

fof(f19,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f80,plain,
    ( spl7_1
    | spl7_2
    | spl7_3 ),
    inference(avatar_split_clause,[],[f18,f77,f73,f69])).

fof(f18,plain,
    ( sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:10:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (27268)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (27276)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  % (27267)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (27287)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (27263)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (27292)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (27265)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (27264)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (27292)Refutation not found, incomplete strategy% (27292)------------------------------
% 0.20/0.53  % (27292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (27264)Refutation not found, incomplete strategy% (27264)------------------------------
% 0.20/0.53  % (27264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (27264)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (27264)Memory used [KB]: 1663
% 0.20/0.53  % (27264)Time elapsed: 0.123 s
% 0.20/0.53  % (27264)------------------------------
% 0.20/0.53  % (27264)------------------------------
% 0.20/0.53  % (27290)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (27291)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (27292)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (27292)Memory used [KB]: 10874
% 0.20/0.53  % (27292)Time elapsed: 0.126 s
% 0.20/0.53  % (27292)------------------------------
% 0.20/0.53  % (27292)------------------------------
% 0.20/0.53  % (27285)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (27270)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.53  % (27266)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (27290)Refutation not found, incomplete strategy% (27290)------------------------------
% 0.20/0.53  % (27290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (27290)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (27290)Memory used [KB]: 6268
% 0.20/0.53  % (27290)Time elapsed: 0.131 s
% 0.20/0.53  % (27290)------------------------------
% 0.20/0.53  % (27290)------------------------------
% 0.20/0.53  % (27275)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (27275)Refutation not found, incomplete strategy% (27275)------------------------------
% 0.20/0.53  % (27275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (27284)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (27274)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.54  % (27289)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (27283)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (27280)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.54  % (27276)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f427,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f80,f230,f241,f248,f254,f258,f291,f319,f330,f336,f379,f383,f426])).
% 0.20/0.54  fof(f426,plain,(
% 0.20/0.54    ~spl7_9 | spl7_10),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f401])).
% 0.20/0.54  fof(f401,plain,(
% 0.20/0.54    $false | (~spl7_9 | spl7_10)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f285,f127,f235,f112])).
% 0.20/0.54  fof(f112,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(X1,X2),X3) != X0 | ~r2_hidden(X1,k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0)) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f107])).
% 0.20/0.54  fof(f107,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(X1,X2),X3) != X0 | ~r2_hidden(X1,k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0) | k1_xboole_0 = k1_tarski(X0)) )),
% 0.20/0.54    inference(superposition,[],[f50,f97])).
% 0.20/0.54  fof(f97,plain,(
% 0.20/0.54    ( ! [X1] : (sK5(k1_tarski(X1)) = X1 | k1_xboole_0 = k1_tarski(X1)) )),
% 0.20/0.54    inference(resolution,[],[f95,f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.20/0.54  fof(f95,plain,(
% 0.20/0.54    ( ! [X2,X1] : (~r2_hidden(X1,k1_tarski(X2)) | X1 = X2) )),
% 0.20/0.54    inference(condensation,[],[f94])).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_tarski(X1)) | X0 = X1 | X1 = X2) )),
% 0.20/0.54    inference(resolution,[],[f93,f67])).
% 0.20/0.54  fof(f67,plain,(
% 0.20/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_enumset1(X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 0.20/0.54    inference(equality_resolution,[],[f53])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 0.20/0.54    inference(definition_unfolding,[],[f41,f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.20/0.54    inference(cnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.20/0.54  fof(f93,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_enumset1(X0,X0,X1)) | ~r2_hidden(X1,k1_tarski(X2))) )),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f92])).
% 0.20/0.54  fof(f92,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X0,X1) != k1_enumset1(X0,X0,X1) | ~r2_hidden(X1,k1_tarski(X2)) | r2_hidden(X2,k1_enumset1(X0,X0,X1))) )),
% 0.20/0.54    inference(superposition,[],[f58,f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X0,X1) != k4_xboole_0(k1_enumset1(X0,X0,X1),X2) | ~r2_hidden(X1,X2)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f45,f30,f30])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X3] : (sK5(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(definition_unfolding,[],[f26,f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X3] : (k1_xboole_0 = X0 | ~r2_hidden(X2,X0) | k3_mcart_1(X2,X3,X4) != sK5(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  fof(f235,plain,(
% 0.20/0.54    sK3 = k4_tarski(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) | ~spl7_9),
% 0.20/0.54    inference(avatar_component_clause,[],[f233])).
% 0.20/0.54  fof(f233,plain,(
% 0.20/0.54    spl7_9 <=> sK3 = k4_tarski(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.54  fof(f127,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 0.20/0.54    inference(condensation,[],[f124])).
% 0.20/0.54  fof(f124,plain,(
% 0.20/0.54    ( ! [X8,X9] : (r2_hidden(X8,k1_tarski(X9)) | r2_hidden(X9,k1_tarski(X9))) )),
% 0.20/0.54    inference(resolution,[],[f120,f66])).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    ( ! [X3,X1] : (r2_hidden(X3,k1_enumset1(X3,X3,X1))) )),
% 0.20/0.54    inference(equality_resolution,[],[f65])).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k1_enumset1(X3,X3,X1) != X2) )),
% 0.20/0.54    inference(equality_resolution,[],[f52])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 0.20/0.54    inference(definition_unfolding,[],[f42,f30])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.20/0.54    inference(cnf_transformation,[],[f1])).
% 0.20/0.54  fof(f120,plain,(
% 0.20/0.54    ( ! [X6,X8,X7] : (~r2_hidden(X8,k1_enumset1(X6,X6,X7)) | r2_hidden(X7,k1_tarski(X8)) | r2_hidden(X6,k1_tarski(X8))) )),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f119])).
% 0.20/0.54  fof(f119,plain,(
% 0.20/0.54    ( ! [X6,X8,X7] : (k1_enumset1(X6,X6,X7) != k1_enumset1(X6,X6,X7) | ~r2_hidden(X8,k1_enumset1(X6,X6,X7)) | r2_hidden(X7,k1_tarski(X8)) | r2_hidden(X6,k1_tarski(X8))) )),
% 0.20/0.54    inference(superposition,[],[f35,f57])).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X0,X1) = k4_xboole_0(k1_enumset1(X0,X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f46,f30,f30])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X1,X2) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f6])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f5])).
% 0.20/0.54  fof(f285,plain,(
% 0.20/0.54    k1_xboole_0 != k1_tarski(sK3) | spl7_10),
% 0.20/0.54    inference(avatar_component_clause,[],[f284])).
% 0.20/0.54  fof(f284,plain,(
% 0.20/0.54    spl7_10 <=> k1_xboole_0 = k1_tarski(sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.54  fof(f383,plain,(
% 0.20/0.54    spl7_4 | ~spl7_5 | spl7_6 | spl7_7 | spl7_9 | ~spl7_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f382,f77,f233,f221,f217,f213,f209])).
% 0.20/0.54  fof(f209,plain,(
% 0.20/0.54    spl7_4 <=> k1_xboole_0 = sK0),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.54  fof(f213,plain,(
% 0.20/0.54    spl7_5 <=> m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.54  fof(f217,plain,(
% 0.20/0.54    spl7_6 <=> k1_xboole_0 = sK2),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.54  fof(f221,plain,(
% 0.20/0.54    spl7_7 <=> k1_xboole_0 = sK1),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.54  fof(f77,plain,(
% 0.20/0.54    spl7_3 <=> sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.54  fof(f382,plain,(
% 0.20/0.54    sK3 = k4_tarski(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0 | ~spl7_3),
% 0.20/0.54    inference(superposition,[],[f60,f79])).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) | ~spl7_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f77])).
% 1.39/0.54  fof(f60,plain,(
% 1.39/0.54    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X0) )),
% 1.39/0.54    inference(definition_unfolding,[],[f47,f37,f36])).
% 1.39/0.54  fof(f37,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f8])).
% 1.39/0.54  fof(f8,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.39/0.54  fof(f47,plain,(
% 1.39/0.54    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) )),
% 1.39/0.54    inference(cnf_transformation,[],[f17])).
% 1.39/0.54  fof(f17,plain,(
% 1.39/0.54    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.39/0.54    inference(ennf_transformation,[],[f10])).
% 1.39/0.54  fof(f10,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).
% 1.39/0.54  fof(f379,plain,(
% 1.39/0.54    spl7_10 | ~spl7_15),
% 1.39/0.54    inference(avatar_contradiction_clause,[],[f354])).
% 1.39/0.54  fof(f354,plain,(
% 1.39/0.54    $false | (spl7_10 | ~spl7_15)),
% 1.39/0.54    inference(unit_resulting_resolution,[],[f285,f127,f335,f103])).
% 1.39/0.54  fof(f103,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (k4_tarski(X1,X2) != X0 | ~r2_hidden(X2,k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0)) )),
% 1.39/0.54    inference(duplicate_literal_removal,[],[f98])).
% 1.39/0.54  fof(f98,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (k4_tarski(X1,X2) != X0 | ~r2_hidden(X2,k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0) | k1_xboole_0 = k1_tarski(X0)) )),
% 1.39/0.54    inference(superposition,[],[f24,f96])).
% 1.39/0.54  fof(f96,plain,(
% 1.39/0.54    ( ! [X0] : (sK4(k1_tarski(X0)) = X0 | k1_xboole_0 = k1_tarski(X0)) )),
% 1.39/0.54    inference(resolution,[],[f95,f25])).
% 1.39/0.54  fof(f25,plain,(
% 1.39/0.54    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.39/0.54    inference(cnf_transformation,[],[f15])).
% 1.39/0.54  fof(f15,plain,(
% 1.39/0.54    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.39/0.54    inference(ennf_transformation,[],[f11])).
% 1.39/0.54  fof(f11,axiom,(
% 1.39/0.54    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 1.39/0.54  fof(f24,plain,(
% 1.39/0.54    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK4(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 1.39/0.54    inference(cnf_transformation,[],[f15])).
% 1.39/0.54  fof(f335,plain,(
% 1.39/0.54    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),sK3) | ~spl7_15),
% 1.39/0.54    inference(avatar_component_clause,[],[f333])).
% 1.39/0.54  fof(f333,plain,(
% 1.39/0.54    spl7_15 <=> sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),sK3)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 1.39/0.54  fof(f336,plain,(
% 1.39/0.54    spl7_4 | ~spl7_5 | spl7_6 | spl7_7 | spl7_15 | ~spl7_1),
% 1.39/0.54    inference(avatar_split_clause,[],[f331,f69,f333,f221,f217,f213,f209])).
% 1.39/0.54  fof(f69,plain,(
% 1.39/0.54    spl7_1 <=> sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.39/0.54  fof(f331,plain,(
% 1.39/0.54    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),sK3) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0 | ~spl7_1),
% 1.39/0.54    inference(superposition,[],[f60,f71])).
% 1.39/0.54  fof(f71,plain,(
% 1.39/0.54    sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | ~spl7_1),
% 1.39/0.54    inference(avatar_component_clause,[],[f69])).
% 1.39/0.54  fof(f330,plain,(
% 1.39/0.54    ~spl7_10),
% 1.39/0.54    inference(avatar_contradiction_clause,[],[f327])).
% 1.39/0.54  fof(f327,plain,(
% 1.39/0.54    $false | ~spl7_10),
% 1.39/0.54    inference(unit_resulting_resolution,[],[f81,f326])).
% 1.39/0.54  fof(f326,plain,(
% 1.39/0.54    r2_hidden(sK3,k1_xboole_0) | ~spl7_10),
% 1.39/0.54    inference(superposition,[],[f127,f286])).
% 1.39/0.54  fof(f286,plain,(
% 1.39/0.54    k1_xboole_0 = k1_tarski(sK3) | ~spl7_10),
% 1.39/0.54    inference(avatar_component_clause,[],[f284])).
% 1.39/0.54  fof(f81,plain,(
% 1.39/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.39/0.54    inference(superposition,[],[f29,f61])).
% 1.39/0.54  fof(f61,plain,(
% 1.39/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.39/0.54    inference(equality_resolution,[],[f33])).
% 1.39/0.54  fof(f33,plain,(
% 1.39/0.54    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 1.39/0.54    inference(cnf_transformation,[],[f3])).
% 1.39/0.54  fof(f3,axiom,(
% 1.39/0.54    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.39/0.54  fof(f29,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.39/0.54    inference(cnf_transformation,[],[f4])).
% 1.39/0.54  fof(f4,axiom,(
% 1.39/0.54    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.39/0.54  fof(f319,plain,(
% 1.39/0.54    spl7_11),
% 1.39/0.54    inference(avatar_contradiction_clause,[],[f311])).
% 1.39/0.54  fof(f311,plain,(
% 1.39/0.54    $false | spl7_11),
% 1.39/0.54    inference(unit_resulting_resolution,[],[f290,f66,f290,f120])).
% 1.39/0.54  fof(f290,plain,(
% 1.39/0.54    ~r2_hidden(sK3,k1_tarski(sK3)) | spl7_11),
% 1.39/0.54    inference(avatar_component_clause,[],[f288])).
% 1.39/0.54  fof(f288,plain,(
% 1.39/0.54    spl7_11 <=> r2_hidden(sK3,k1_tarski(sK3))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.39/0.54  fof(f291,plain,(
% 1.39/0.54    spl7_10 | ~spl7_11 | ~spl7_8),
% 1.39/0.54    inference(avatar_split_clause,[],[f263,f225,f288,f284])).
% 1.39/0.54  fof(f225,plain,(
% 1.39/0.54    spl7_8 <=> sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k7_mcart_1(sK0,sK1,sK2,sK3))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.39/0.54  fof(f263,plain,(
% 1.39/0.54    ~r2_hidden(sK3,k1_tarski(sK3)) | k1_xboole_0 = k1_tarski(sK3) | ~spl7_8),
% 1.39/0.54    inference(superposition,[],[f130,f227])).
% 1.39/0.54  fof(f227,plain,(
% 1.39/0.54    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | ~spl7_8),
% 1.39/0.54    inference(avatar_component_clause,[],[f225])).
% 1.39/0.54  fof(f130,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_tarski(k4_tarski(k4_tarski(X1,X0),X2))) | k1_xboole_0 = k1_tarski(k4_tarski(k4_tarski(X1,X0),X2))) )),
% 1.39/0.54    inference(equality_resolution,[],[f111])).
% 1.39/0.54  fof(f111,plain,(
% 1.39/0.54    ( ! [X6,X4,X7,X5] : (k4_tarski(k4_tarski(X5,X6),X7) != X4 | ~r2_hidden(X6,k1_tarski(X4)) | k1_xboole_0 = k1_tarski(X4)) )),
% 1.39/0.54    inference(duplicate_literal_removal,[],[f108])).
% 1.39/0.54  fof(f108,plain,(
% 1.39/0.54    ( ! [X6,X4,X7,X5] : (k4_tarski(k4_tarski(X5,X6),X7) != X4 | ~r2_hidden(X6,k1_tarski(X4)) | k1_xboole_0 = k1_tarski(X4) | k1_xboole_0 = k1_tarski(X4)) )),
% 1.39/0.54    inference(superposition,[],[f49,f97])).
% 1.39/0.54  fof(f49,plain,(
% 1.39/0.54    ( ! [X4,X2,X0,X3] : (sK5(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 1.39/0.54    inference(definition_unfolding,[],[f27,f36])).
% 1.39/0.54  fof(f27,plain,(
% 1.39/0.54    ( ! [X4,X2,X0,X3] : (k1_xboole_0 = X0 | ~r2_hidden(X3,X0) | k3_mcart_1(X2,X3,X4) != sK5(X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f16])).
% 1.39/0.54  fof(f258,plain,(
% 1.39/0.54    spl7_4 | ~spl7_5 | spl7_6 | spl7_7 | spl7_8 | ~spl7_2),
% 1.39/0.54    inference(avatar_split_clause,[],[f257,f73,f225,f221,f217,f213,f209])).
% 1.39/0.54  fof(f73,plain,(
% 1.39/0.54    spl7_2 <=> sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.39/0.54  fof(f257,plain,(
% 1.39/0.54    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0 | ~spl7_2),
% 1.39/0.54    inference(superposition,[],[f60,f75])).
% 1.39/0.54  fof(f75,plain,(
% 1.39/0.54    sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | ~spl7_2),
% 1.39/0.54    inference(avatar_component_clause,[],[f73])).
% 1.39/0.54  fof(f254,plain,(
% 1.39/0.54    ~spl7_7),
% 1.39/0.54    inference(avatar_contradiction_clause,[],[f250])).
% 1.39/0.54  fof(f250,plain,(
% 1.39/0.54    $false | ~spl7_7),
% 1.39/0.54    inference(subsumption_resolution,[],[f21,f223])).
% 1.39/0.54  fof(f223,plain,(
% 1.39/0.54    k1_xboole_0 = sK1 | ~spl7_7),
% 1.39/0.54    inference(avatar_component_clause,[],[f221])).
% 1.39/0.54  fof(f21,plain,(
% 1.39/0.54    k1_xboole_0 != sK1),
% 1.39/0.54    inference(cnf_transformation,[],[f14])).
% 1.39/0.54  fof(f14,plain,(
% 1.39/0.54    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.39/0.54    inference(ennf_transformation,[],[f13])).
% 1.39/0.54  fof(f13,negated_conjecture,(
% 1.39/0.54    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.39/0.54    inference(negated_conjecture,[],[f12])).
% 1.39/0.54  fof(f12,conjecture,(
% 1.39/0.54    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).
% 1.39/0.54  fof(f248,plain,(
% 1.39/0.54    ~spl7_6),
% 1.39/0.54    inference(avatar_contradiction_clause,[],[f244])).
% 1.39/0.54  fof(f244,plain,(
% 1.39/0.54    $false | ~spl7_6),
% 1.39/0.54    inference(subsumption_resolution,[],[f22,f219])).
% 1.39/0.54  fof(f219,plain,(
% 1.39/0.54    k1_xboole_0 = sK2 | ~spl7_6),
% 1.39/0.54    inference(avatar_component_clause,[],[f217])).
% 1.39/0.54  fof(f22,plain,(
% 1.39/0.54    k1_xboole_0 != sK2),
% 1.39/0.54    inference(cnf_transformation,[],[f14])).
% 1.39/0.54  fof(f241,plain,(
% 1.39/0.54    ~spl7_4),
% 1.39/0.54    inference(avatar_contradiction_clause,[],[f237])).
% 1.39/0.54  fof(f237,plain,(
% 1.39/0.54    $false | ~spl7_4),
% 1.39/0.54    inference(subsumption_resolution,[],[f20,f211])).
% 1.39/0.54  fof(f211,plain,(
% 1.39/0.54    k1_xboole_0 = sK0 | ~spl7_4),
% 1.39/0.54    inference(avatar_component_clause,[],[f209])).
% 1.39/0.54  fof(f20,plain,(
% 1.39/0.54    k1_xboole_0 != sK0),
% 1.39/0.54    inference(cnf_transformation,[],[f14])).
% 1.39/0.54  fof(f230,plain,(
% 1.39/0.54    spl7_5),
% 1.39/0.54    inference(avatar_contradiction_clause,[],[f229])).
% 1.39/0.54  fof(f229,plain,(
% 1.39/0.54    $false | spl7_5),
% 1.39/0.54    inference(subsumption_resolution,[],[f48,f215])).
% 1.39/0.54  fof(f215,plain,(
% 1.39/0.54    ~m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | spl7_5),
% 1.39/0.54    inference(avatar_component_clause,[],[f213])).
% 1.39/0.54  fof(f48,plain,(
% 1.39/0.54    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.39/0.54    inference(definition_unfolding,[],[f19,f37])).
% 1.39/0.54  fof(f19,plain,(
% 1.39/0.54    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.39/0.54    inference(cnf_transformation,[],[f14])).
% 1.39/0.54  fof(f80,plain,(
% 1.39/0.54    spl7_1 | spl7_2 | spl7_3),
% 1.39/0.54    inference(avatar_split_clause,[],[f18,f77,f73,f69])).
% 1.39/0.54  fof(f18,plain,(
% 1.39/0.54    sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)),
% 1.39/0.54    inference(cnf_transformation,[],[f14])).
% 1.39/0.54  % SZS output end Proof for theBenchmark
% 1.39/0.54  % (27276)------------------------------
% 1.39/0.54  % (27276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (27276)Termination reason: Refutation
% 1.39/0.54  
% 1.39/0.54  % (27276)Memory used [KB]: 6524
% 1.39/0.54  % (27276)Time elapsed: 0.121 s
% 1.39/0.54  % (27279)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.39/0.54  % (27276)------------------------------
% 1.39/0.54  % (27276)------------------------------
% 1.39/0.54  % (27260)Success in time 0.183 s
%------------------------------------------------------------------------------
