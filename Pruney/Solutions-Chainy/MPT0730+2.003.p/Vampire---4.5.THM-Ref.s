%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:13 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 302 expanded)
%              Number of leaves         :   29 ( 100 expanded)
%              Depth                    :   13
%              Number of atoms          :  321 ( 602 expanded)
%              Number of equality atoms :   61 ( 235 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f392,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f109,f110,f151,f211,f331,f353,f359,f391])).

fof(f391,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f390])).

fof(f390,plain,
    ( $false
    | spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f386,f107])).

fof(f107,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_4
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f386,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl4_3 ),
    inference(resolution,[],[f370,f85])).

fof(f85,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f53,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f370,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))))
        | ~ r2_hidden(sK1,X0) )
    | spl4_3 ),
    inference(resolution,[],[f104,f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f104,plain,
    ( ~ r2_hidden(sK1,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_3
  <=> r2_hidden(sK1,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f359,plain,
    ( spl4_4
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f356,f208,f106])).

fof(f208,plain,
    ( spl4_7
  <=> sP0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f356,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl4_7 ),
    inference(resolution,[],[f210,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X0)
        & r2_hidden(X1,X2) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X1,X2,X0] :
      ( ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ sP0(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X1,X2,X0] :
      ( ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ sP0(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f210,plain,
    ( sP0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1,sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f208])).

fof(f353,plain,
    ( spl4_2
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f352])).

fof(f352,plain,
    ( $false
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f347,f89])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f347,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl4_2
    | ~ spl4_6 ),
    inference(resolution,[],[f340,f346])).

fof(f346,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f345,f99])).

fof(f99,plain,
    ( sK1 != sK2
    | spl4_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_2
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f345,plain,
    ( sK1 = sK2
    | ~ r1_tarski(sK2,sK1)
    | ~ spl4_6 ),
    inference(resolution,[],[f341,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f341,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f206,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_enumset1(X0,X0,X0,X0,X0))
      | r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f56,f84])).

fof(f84,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f52,f76])).

fof(f52,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f206,plain,
    ( r2_hidden(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl4_6
  <=> r2_hidden(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f340,plain,
    ( ! [X28] :
        ( r1_tarski(sK2,X28)
        | ~ r1_tarski(sK1,X28) )
    | ~ spl4_6 ),
    inference(resolution,[],[f206,f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_enumset1(X0,X0,X0,X0,X0))
      | ~ r1_tarski(X2,X1)
      | r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f67,f83])).

fof(f83,plain,(
    ! [X0] : k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f49,f77])).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f75])).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).

fof(f331,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f330])).

fof(f330,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f329,f89])).

fof(f329,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl4_5 ),
    inference(resolution,[],[f326,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f326,plain,
    ( r2_hidden(sK2,sK2)
    | spl4_5 ),
    inference(duplicate_literal_removal,[],[f325])).

fof(f325,plain,
    ( r2_hidden(sK2,sK2)
    | r2_hidden(sK2,sK2)
    | spl4_5 ),
    inference(resolution,[],[f165,f202])).

fof(f202,plain,
    ( ~ r1_xboole_0(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl4_5
  <=> r1_xboole_0(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X2))
      | r2_hidden(X2,X0)
      | r2_hidden(X1,X0) ) ),
    inference(trivial_inequality_removal,[],[f164])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( X0 != X0
      | r1_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X2))
      | r2_hidden(X2,X0)
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f61,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k3_enumset1(X0,X0,X0,X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f68,f75])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f211,plain,
    ( ~ spl4_5
    | spl4_6
    | spl4_7
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f197,f102,f208,f204,f200])).

fof(f197,plain,
    ( sP0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1,sK2)
    | r2_hidden(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | ~ r1_xboole_0(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | ~ spl4_3 ),
    inference(resolution,[],[f88,f103])).

fof(f103,plain,
    ( r2_hidden(sK1,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
      | sP0(X1,X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f71,f76])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | sP0(X1,X2,X0)
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | sP0(X1,X2,X0)
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_folding,[],[f29,f30])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).

fof(f151,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f95,f82])).

fof(f82,plain,(
    ! [X0] : r2_hidden(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f48,f78])).

fof(f78,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f51,f76,f77])).

fof(f51,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f48,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f95,plain,
    ( ~ r2_hidden(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl4_1
  <=> r2_hidden(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f110,plain,
    ( spl4_3
    | spl4_4
    | spl4_2 ),
    inference(avatar_split_clause,[],[f81,f97,f106,f102])).

fof(f81,plain,
    ( sK1 = sK2
    | r2_hidden(sK1,sK2)
    | r2_hidden(sK1,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f45,f78])).

fof(f45,plain,
    ( sK1 = sK2
    | r2_hidden(sK1,sK2)
    | r2_hidden(sK1,k1_ordinal1(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ( sK1 != sK2
        & ~ r2_hidden(sK1,sK2) )
      | ~ r2_hidden(sK1,k1_ordinal1(sK2)) )
    & ( sK1 = sK2
      | r2_hidden(sK1,sK2)
      | r2_hidden(sK1,k1_ordinal1(sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f33,f34])).

fof(f34,plain,
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

fof(f33,plain,(
    ? [X0,X1] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k1_ordinal1(X1)) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k1_ordinal1(X1)) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <~> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,k1_ordinal1(X1))
      <=> ( X0 = X1
          | r2_hidden(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f109,plain,
    ( ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f80,f106,f102])).

fof(f80,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f46,f78])).

fof(f46,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,k1_ordinal1(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f100,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f91,f97,f93])).

fof(f91,plain,
    ( sK1 != sK2
    | ~ r2_hidden(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ),
    inference(inner_rewriting,[],[f79])).

fof(f79,plain,
    ( sK1 != sK2
    | ~ r2_hidden(sK1,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f47,f78])).

fof(f47,plain,
    ( sK1 != sK2
    | ~ r2_hidden(sK1,k1_ordinal1(sK2)) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:00:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (1450)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (1458)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (1441)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (1465)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (1442)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (1451)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (1464)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (1443)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (1453)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (1438)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.23/0.52  % (1457)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.23/0.52  % (1456)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.23/0.52  % (1445)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.23/0.52  % (1448)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.23/0.53  % (1437)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.23/0.53  % (1448)Refutation not found, incomplete strategy% (1448)------------------------------
% 1.23/0.53  % (1448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (1448)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  
% 1.23/0.53  % (1448)Memory used [KB]: 10618
% 1.23/0.53  % (1448)Time elapsed: 0.125 s
% 1.23/0.53  % (1448)------------------------------
% 1.23/0.53  % (1448)------------------------------
% 1.23/0.53  % (1455)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.23/0.53  % (1449)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.23/0.53  % (1436)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.23/0.53  % (1440)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.23/0.53  % (1444)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.23/0.53  % (1466)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.23/0.53  % (1460)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.34/0.54  % (1452)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.34/0.54  % (1447)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.34/0.54  % (1447)Refutation not found, incomplete strategy% (1447)------------------------------
% 1.34/0.54  % (1447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (1447)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (1447)Memory used [KB]: 10618
% 1.34/0.54  % (1447)Time elapsed: 0.132 s
% 1.34/0.54  % (1447)------------------------------
% 1.34/0.54  % (1447)------------------------------
% 1.34/0.54  % (1446)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.34/0.54  % (1462)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.34/0.54  % (1461)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.34/0.54  % (1459)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.34/0.55  % (1463)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.56  % (1454)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.34/0.56  % (1464)Refutation found. Thanks to Tanya!
% 1.34/0.56  % SZS status Theorem for theBenchmark
% 1.34/0.56  % SZS output start Proof for theBenchmark
% 1.34/0.56  fof(f392,plain,(
% 1.34/0.56    $false),
% 1.34/0.56    inference(avatar_sat_refutation,[],[f100,f109,f110,f151,f211,f331,f353,f359,f391])).
% 1.34/0.56  fof(f391,plain,(
% 1.34/0.56    spl4_3 | ~spl4_4),
% 1.34/0.56    inference(avatar_contradiction_clause,[],[f390])).
% 1.34/0.56  fof(f390,plain,(
% 1.34/0.56    $false | (spl4_3 | ~spl4_4)),
% 1.34/0.56    inference(subsumption_resolution,[],[f386,f107])).
% 1.34/0.56  fof(f107,plain,(
% 1.34/0.56    r2_hidden(sK1,sK2) | ~spl4_4),
% 1.34/0.56    inference(avatar_component_clause,[],[f106])).
% 1.34/0.56  fof(f106,plain,(
% 1.34/0.56    spl4_4 <=> r2_hidden(sK1,sK2)),
% 1.34/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.34/0.56  fof(f386,plain,(
% 1.34/0.56    ~r2_hidden(sK1,sK2) | spl4_3),
% 1.34/0.56    inference(resolution,[],[f370,f85])).
% 1.34/0.56  fof(f85,plain,(
% 1.34/0.56    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.34/0.56    inference(definition_unfolding,[],[f53,f76])).
% 1.34/0.56  fof(f76,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.34/0.56    inference(definition_unfolding,[],[f54,f75])).
% 1.34/0.56  fof(f75,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.34/0.56    inference(definition_unfolding,[],[f55,f74])).
% 1.34/0.56  fof(f74,plain,(
% 1.34/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.34/0.56    inference(definition_unfolding,[],[f66,f73])).
% 1.34/0.56  fof(f73,plain,(
% 1.34/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f10])).
% 1.34/0.56  fof(f10,axiom,(
% 1.34/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.34/0.56  fof(f66,plain,(
% 1.34/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f9])).
% 1.34/0.56  fof(f9,axiom,(
% 1.34/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.34/0.56  fof(f55,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f8])).
% 1.34/0.56  fof(f8,axiom,(
% 1.34/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.34/0.56  fof(f54,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.34/0.56    inference(cnf_transformation,[],[f12])).
% 1.34/0.56  fof(f12,axiom,(
% 1.34/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.34/0.56  fof(f53,plain,(
% 1.34/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.34/0.56    inference(cnf_transformation,[],[f5])).
% 1.34/0.56  fof(f5,axiom,(
% 1.34/0.56    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.34/0.56  fof(f370,plain,(
% 1.34/0.56    ( ! [X0] : (~r1_tarski(X0,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) | ~r2_hidden(sK1,X0)) ) | spl4_3),
% 1.34/0.56    inference(resolution,[],[f104,f62])).
% 1.34/0.56  fof(f62,plain,(
% 1.34/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f42])).
% 1.34/0.56  fof(f42,plain,(
% 1.34/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.34/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).
% 1.34/0.56  fof(f41,plain,(
% 1.34/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.34/0.56    introduced(choice_axiom,[])).
% 1.34/0.56  fof(f40,plain,(
% 1.34/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.34/0.56    inference(rectify,[],[f39])).
% 1.34/0.56  fof(f39,plain,(
% 1.34/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.34/0.56    inference(nnf_transformation,[],[f24])).
% 1.34/0.56  fof(f24,plain,(
% 1.34/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.34/0.56    inference(ennf_transformation,[],[f1])).
% 1.34/0.56  fof(f1,axiom,(
% 1.34/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.34/0.56  fof(f104,plain,(
% 1.34/0.56    ~r2_hidden(sK1,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) | spl4_3),
% 1.34/0.56    inference(avatar_component_clause,[],[f102])).
% 1.34/0.56  fof(f102,plain,(
% 1.34/0.56    spl4_3 <=> r2_hidden(sK1,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))))),
% 1.34/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.34/0.56  fof(f359,plain,(
% 1.34/0.56    spl4_4 | ~spl4_7),
% 1.34/0.56    inference(avatar_split_clause,[],[f356,f208,f106])).
% 1.34/0.56  fof(f208,plain,(
% 1.34/0.56    spl4_7 <=> sP0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1,sK2)),
% 1.34/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.34/0.56  fof(f356,plain,(
% 1.34/0.56    r2_hidden(sK1,sK2) | ~spl4_7),
% 1.34/0.56    inference(resolution,[],[f210,f69])).
% 1.34/0.56  fof(f69,plain,(
% 1.34/0.56    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X2)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f44])).
% 1.34/0.56  fof(f44,plain,(
% 1.34/0.56    ! [X0,X1,X2] : ((~r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2))),
% 1.34/0.56    inference(rectify,[],[f43])).
% 1.34/0.56  fof(f43,plain,(
% 1.34/0.56    ! [X1,X2,X0] : ((~r2_hidden(X2,X1) & r2_hidden(X2,X0)) | ~sP0(X1,X2,X0))),
% 1.34/0.56    inference(nnf_transformation,[],[f30])).
% 1.34/0.56  fof(f30,plain,(
% 1.34/0.56    ! [X1,X2,X0] : ((~r2_hidden(X2,X1) & r2_hidden(X2,X0)) | ~sP0(X1,X2,X0))),
% 1.34/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.34/0.56  fof(f210,plain,(
% 1.34/0.56    sP0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1,sK2) | ~spl4_7),
% 1.34/0.56    inference(avatar_component_clause,[],[f208])).
% 1.34/0.56  fof(f353,plain,(
% 1.34/0.56    spl4_2 | ~spl4_6),
% 1.34/0.56    inference(avatar_contradiction_clause,[],[f352])).
% 1.34/0.56  fof(f352,plain,(
% 1.34/0.56    $false | (spl4_2 | ~spl4_6)),
% 1.34/0.56    inference(subsumption_resolution,[],[f347,f89])).
% 1.34/0.56  fof(f89,plain,(
% 1.34/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.34/0.56    inference(equality_resolution,[],[f58])).
% 1.34/0.56  fof(f58,plain,(
% 1.34/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.34/0.56    inference(cnf_transformation,[],[f37])).
% 1.34/0.56  fof(f37,plain,(
% 1.34/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.34/0.56    inference(flattening,[],[f36])).
% 1.34/0.56  fof(f36,plain,(
% 1.34/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.34/0.56    inference(nnf_transformation,[],[f4])).
% 1.34/0.56  fof(f4,axiom,(
% 1.34/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.34/0.56  fof(f347,plain,(
% 1.34/0.56    ~r1_tarski(sK1,sK1) | (spl4_2 | ~spl4_6)),
% 1.34/0.56    inference(resolution,[],[f340,f346])).
% 1.34/0.56  fof(f346,plain,(
% 1.34/0.56    ~r1_tarski(sK2,sK1) | (spl4_2 | ~spl4_6)),
% 1.34/0.56    inference(subsumption_resolution,[],[f345,f99])).
% 1.34/0.56  fof(f99,plain,(
% 1.34/0.56    sK1 != sK2 | spl4_2),
% 1.34/0.56    inference(avatar_component_clause,[],[f97])).
% 1.34/0.56  fof(f97,plain,(
% 1.34/0.56    spl4_2 <=> sK1 = sK2),
% 1.34/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.34/0.56  fof(f345,plain,(
% 1.34/0.56    sK1 = sK2 | ~r1_tarski(sK2,sK1) | ~spl4_6),
% 1.34/0.56    inference(resolution,[],[f341,f59])).
% 1.34/0.56  fof(f59,plain,(
% 1.34/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f37])).
% 1.34/0.56  fof(f341,plain,(
% 1.34/0.56    r1_tarski(sK1,sK2) | ~spl4_6),
% 1.34/0.56    inference(resolution,[],[f206,f127])).
% 1.34/0.56  fof(f127,plain,(
% 1.34/0.56    ( ! [X0,X1] : (~r2_hidden(X1,k3_enumset1(X0,X0,X0,X0,X0)) | r1_tarski(X1,X0)) )),
% 1.34/0.56    inference(superposition,[],[f56,f84])).
% 1.34/0.56  fof(f84,plain,(
% 1.34/0.56    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0) )),
% 1.34/0.56    inference(definition_unfolding,[],[f52,f76])).
% 1.34/0.56  fof(f52,plain,(
% 1.34/0.56    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.34/0.56    inference(cnf_transformation,[],[f21])).
% 1.34/0.56  fof(f21,plain,(
% 1.34/0.56    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.34/0.56    inference(rectify,[],[f2])).
% 1.34/0.56  fof(f2,axiom,(
% 1.34/0.56    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.34/0.56  fof(f56,plain,(
% 1.34/0.56    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f23])).
% 1.34/0.56  fof(f23,plain,(
% 1.34/0.56    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 1.34/0.56    inference(ennf_transformation,[],[f11])).
% 1.34/0.56  fof(f11,axiom,(
% 1.34/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 1.34/0.56  fof(f206,plain,(
% 1.34/0.56    r2_hidden(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | ~spl4_6),
% 1.34/0.56    inference(avatar_component_clause,[],[f204])).
% 1.34/0.56  fof(f204,plain,(
% 1.34/0.56    spl4_6 <=> r2_hidden(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 1.34/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.34/0.56  fof(f340,plain,(
% 1.34/0.56    ( ! [X28] : (r1_tarski(sK2,X28) | ~r1_tarski(sK1,X28)) ) | ~spl4_6),
% 1.34/0.56    inference(resolution,[],[f206,f137])).
% 1.34/0.56  fof(f137,plain,(
% 1.34/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_enumset1(X0,X0,X0,X0,X0)) | ~r1_tarski(X2,X1) | r1_tarski(X0,X1)) )),
% 1.34/0.56    inference(superposition,[],[f67,f83])).
% 1.34/0.56  fof(f83,plain,(
% 1.34/0.56    ( ! [X0] : (k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X0)) = X0) )),
% 1.34/0.56    inference(definition_unfolding,[],[f49,f77])).
% 1.34/0.56  fof(f77,plain,(
% 1.34/0.56    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.34/0.56    inference(definition_unfolding,[],[f50,f75])).
% 1.34/0.56  fof(f50,plain,(
% 1.34/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f7])).
% 1.34/0.56  fof(f7,axiom,(
% 1.34/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.34/0.56  fof(f49,plain,(
% 1.34/0.56    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 1.34/0.56    inference(cnf_transformation,[],[f14])).
% 1.34/0.56  fof(f14,axiom,(
% 1.34/0.56    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 1.34/0.56  fof(f67,plain,(
% 1.34/0.56    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f27])).
% 1.34/0.56  fof(f27,plain,(
% 1.34/0.56    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 1.34/0.56    inference(flattening,[],[f26])).
% 1.34/0.56  fof(f26,plain,(
% 1.34/0.56    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 1.34/0.56    inference(ennf_transformation,[],[f15])).
% 1.34/0.56  fof(f15,axiom,(
% 1.34/0.56    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).
% 1.34/0.56  fof(f331,plain,(
% 1.34/0.56    spl4_5),
% 1.34/0.56    inference(avatar_contradiction_clause,[],[f330])).
% 1.34/0.56  fof(f330,plain,(
% 1.34/0.56    $false | spl4_5),
% 1.34/0.56    inference(subsumption_resolution,[],[f329,f89])).
% 1.34/0.56  fof(f329,plain,(
% 1.34/0.56    ~r1_tarski(sK2,sK2) | spl4_5),
% 1.34/0.56    inference(resolution,[],[f326,f65])).
% 1.34/0.56  fof(f65,plain,(
% 1.34/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f25])).
% 1.34/0.56  fof(f25,plain,(
% 1.34/0.56    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.34/0.56    inference(ennf_transformation,[],[f18])).
% 1.34/0.56  fof(f18,axiom,(
% 1.34/0.56    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.34/0.56  fof(f326,plain,(
% 1.34/0.56    r2_hidden(sK2,sK2) | spl4_5),
% 1.34/0.56    inference(duplicate_literal_removal,[],[f325])).
% 1.34/0.56  fof(f325,plain,(
% 1.34/0.56    r2_hidden(sK2,sK2) | r2_hidden(sK2,sK2) | spl4_5),
% 1.34/0.56    inference(resolution,[],[f165,f202])).
% 1.34/0.56  fof(f202,plain,(
% 1.34/0.56    ~r1_xboole_0(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | spl4_5),
% 1.34/0.56    inference(avatar_component_clause,[],[f200])).
% 1.34/0.56  fof(f200,plain,(
% 1.34/0.56    spl4_5 <=> r1_xboole_0(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 1.34/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.34/0.56  fof(f165,plain,(
% 1.34/0.56    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X2)) | r2_hidden(X2,X0) | r2_hidden(X1,X0)) )),
% 1.34/0.56    inference(trivial_inequality_removal,[],[f164])).
% 1.34/0.56  fof(f164,plain,(
% 1.34/0.56    ( ! [X2,X0,X1] : (X0 != X0 | r1_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X2)) | r2_hidden(X2,X0) | r2_hidden(X1,X0)) )),
% 1.34/0.56    inference(superposition,[],[f61,f86])).
% 1.34/0.56  fof(f86,plain,(
% 1.34/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k3_enumset1(X0,X0,X0,X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.34/0.56    inference(definition_unfolding,[],[f68,f75])).
% 1.34/0.58  fof(f68,plain,(
% 1.34/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f28])).
% 1.34/0.58  fof(f28,plain,(
% 1.34/0.58    ! [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2))),
% 1.34/0.58    inference(ennf_transformation,[],[f13])).
% 1.34/0.58  fof(f13,axiom,(
% 1.34/0.58    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 1.34/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 1.34/0.58  fof(f61,plain,(
% 1.34/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f38])).
% 1.34/0.58  fof(f38,plain,(
% 1.34/0.58    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.34/0.58    inference(nnf_transformation,[],[f6])).
% 1.34/0.58  fof(f6,axiom,(
% 1.34/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.34/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.34/0.58  fof(f211,plain,(
% 1.34/0.58    ~spl4_5 | spl4_6 | spl4_7 | ~spl4_3),
% 1.34/0.58    inference(avatar_split_clause,[],[f197,f102,f208,f204,f200])).
% 1.34/0.58  fof(f197,plain,(
% 1.34/0.58    sP0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1,sK2) | r2_hidden(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | ~r1_xboole_0(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | ~spl4_3),
% 1.34/0.58    inference(resolution,[],[f88,f103])).
% 1.34/0.58  fof(f103,plain,(
% 1.34/0.58    r2_hidden(sK1,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) | ~spl4_3),
% 1.34/0.58    inference(avatar_component_clause,[],[f102])).
% 1.34/0.58  fof(f88,plain,(
% 1.34/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) | sP0(X1,X2,X0) | r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 1.34/0.58    inference(definition_unfolding,[],[f71,f76])).
% 1.34/0.58  fof(f71,plain,(
% 1.34/0.58    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | sP0(X1,X2,X0) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f31])).
% 1.34/0.58  fof(f31,plain,(
% 1.34/0.58    ! [X0,X1,X2] : ((~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | sP0(X1,X2,X0) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 1.34/0.58    inference(definition_folding,[],[f29,f30])).
% 1.34/0.58  fof(f29,plain,(
% 1.34/0.58    ! [X0,X1,X2] : ((~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 1.34/0.58    inference(ennf_transformation,[],[f3])).
% 1.34/0.58  fof(f3,axiom,(
% 1.34/0.58    ! [X0,X1,X2] : ~(~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & ~(~r2_hidden(X2,X1) & r2_hidden(X2,X0)) & r2_hidden(X2,k2_xboole_0(X0,X1)) & r1_xboole_0(X0,X1))),
% 1.34/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).
% 1.34/0.58  fof(f151,plain,(
% 1.34/0.58    spl4_1),
% 1.34/0.58    inference(avatar_contradiction_clause,[],[f148])).
% 1.34/0.58  fof(f148,plain,(
% 1.34/0.58    $false | spl4_1),
% 1.34/0.58    inference(subsumption_resolution,[],[f95,f82])).
% 1.34/0.58  fof(f82,plain,(
% 1.34/0.58    ( ! [X0] : (r2_hidden(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0))))) )),
% 1.34/0.58    inference(definition_unfolding,[],[f48,f78])).
% 1.34/0.58  fof(f78,plain,(
% 1.34/0.58    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0)))) )),
% 1.34/0.58    inference(definition_unfolding,[],[f51,f76,f77])).
% 1.34/0.58  fof(f51,plain,(
% 1.34/0.58    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.34/0.58    inference(cnf_transformation,[],[f16])).
% 1.34/0.58  fof(f16,axiom,(
% 1.34/0.58    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.34/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.34/0.58  fof(f48,plain,(
% 1.34/0.58    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 1.34/0.58    inference(cnf_transformation,[],[f17])).
% 1.34/0.58  fof(f17,axiom,(
% 1.34/0.58    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 1.34/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 1.34/0.58  fof(f95,plain,(
% 1.34/0.58    ~r2_hidden(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) | spl4_1),
% 1.34/0.58    inference(avatar_component_clause,[],[f93])).
% 1.34/0.58  fof(f93,plain,(
% 1.34/0.58    spl4_1 <=> r2_hidden(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))),
% 1.34/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.34/0.58  fof(f110,plain,(
% 1.34/0.58    spl4_3 | spl4_4 | spl4_2),
% 1.34/0.58    inference(avatar_split_clause,[],[f81,f97,f106,f102])).
% 1.34/0.58  fof(f81,plain,(
% 1.34/0.58    sK1 = sK2 | r2_hidden(sK1,sK2) | r2_hidden(sK1,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))))),
% 1.34/0.58    inference(definition_unfolding,[],[f45,f78])).
% 1.34/0.58  fof(f45,plain,(
% 1.34/0.58    sK1 = sK2 | r2_hidden(sK1,sK2) | r2_hidden(sK1,k1_ordinal1(sK2))),
% 1.34/0.58    inference(cnf_transformation,[],[f35])).
% 1.34/0.58  fof(f35,plain,(
% 1.34/0.58    ((sK1 != sK2 & ~r2_hidden(sK1,sK2)) | ~r2_hidden(sK1,k1_ordinal1(sK2))) & (sK1 = sK2 | r2_hidden(sK1,sK2) | r2_hidden(sK1,k1_ordinal1(sK2)))),
% 1.34/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f33,f34])).
% 1.34/0.58  fof(f34,plain,(
% 1.34/0.58    ? [X0,X1] : (((X0 != X1 & ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))) & (X0 = X1 | r2_hidden(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) => (((sK1 != sK2 & ~r2_hidden(sK1,sK2)) | ~r2_hidden(sK1,k1_ordinal1(sK2))) & (sK1 = sK2 | r2_hidden(sK1,sK2) | r2_hidden(sK1,k1_ordinal1(sK2))))),
% 1.34/0.58    introduced(choice_axiom,[])).
% 1.34/0.58  fof(f33,plain,(
% 1.34/0.58    ? [X0,X1] : (((X0 != X1 & ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))) & (X0 = X1 | r2_hidden(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))))),
% 1.34/0.58    inference(flattening,[],[f32])).
% 1.34/0.58  fof(f32,plain,(
% 1.34/0.58    ? [X0,X1] : (((X0 != X1 & ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | r2_hidden(X0,k1_ordinal1(X1))))),
% 1.34/0.58    inference(nnf_transformation,[],[f22])).
% 1.34/0.58  fof(f22,plain,(
% 1.34/0.58    ? [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <~> (X0 = X1 | r2_hidden(X0,X1)))),
% 1.34/0.58    inference(ennf_transformation,[],[f20])).
% 1.34/0.58  fof(f20,negated_conjecture,(
% 1.34/0.58    ~! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 1.34/0.58    inference(negated_conjecture,[],[f19])).
% 1.34/0.58  fof(f19,conjecture,(
% 1.34/0.58    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 1.34/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 1.34/0.58  fof(f109,plain,(
% 1.34/0.58    ~spl4_3 | ~spl4_4),
% 1.34/0.58    inference(avatar_split_clause,[],[f80,f106,f102])).
% 1.34/0.58  fof(f80,plain,(
% 1.34/0.58    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK1,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))))),
% 1.34/0.58    inference(definition_unfolding,[],[f46,f78])).
% 1.34/0.58  fof(f46,plain,(
% 1.34/0.58    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK1,k1_ordinal1(sK2))),
% 1.34/0.58    inference(cnf_transformation,[],[f35])).
% 1.34/0.58  fof(f100,plain,(
% 1.34/0.58    ~spl4_1 | ~spl4_2),
% 1.34/0.58    inference(avatar_split_clause,[],[f91,f97,f93])).
% 1.34/0.58  fof(f91,plain,(
% 1.34/0.58    sK1 != sK2 | ~r2_hidden(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))),
% 1.34/0.58    inference(inner_rewriting,[],[f79])).
% 1.34/0.58  fof(f79,plain,(
% 1.34/0.58    sK1 != sK2 | ~r2_hidden(sK1,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))))),
% 1.34/0.58    inference(definition_unfolding,[],[f47,f78])).
% 1.34/0.58  fof(f47,plain,(
% 1.34/0.58    sK1 != sK2 | ~r2_hidden(sK1,k1_ordinal1(sK2))),
% 1.34/0.58    inference(cnf_transformation,[],[f35])).
% 1.34/0.58  % SZS output end Proof for theBenchmark
% 1.34/0.58  % (1464)------------------------------
% 1.34/0.58  % (1464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.58  % (1464)Termination reason: Refutation
% 1.34/0.58  
% 1.34/0.58  % (1464)Memory used [KB]: 6396
% 1.34/0.58  % (1464)Time elapsed: 0.143 s
% 1.34/0.58  % (1464)------------------------------
% 1.34/0.58  % (1464)------------------------------
% 1.34/0.58  % (1433)Success in time 0.221 s
%------------------------------------------------------------------------------
