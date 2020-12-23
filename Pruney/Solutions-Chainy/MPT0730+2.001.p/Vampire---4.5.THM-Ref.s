%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:12 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 250 expanded)
%              Number of leaves         :   22 (  83 expanded)
%              Depth                    :   14
%              Number of atoms          :  285 ( 514 expanded)
%              Number of equality atoms :   82 ( 238 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f265,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f106,f107,f110,f132,f264])).

fof(f264,plain,
    ( ~ spl4_1
    | spl4_2
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | ~ spl4_1
    | spl4_2
    | spl4_3 ),
    inference(subsumption_resolution,[],[f255,f89])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f255,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ spl4_1
    | spl4_2
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f237,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f237,plain,
    ( r2_hidden(sK1,sK1)
    | ~ spl4_1
    | spl4_2
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f180,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f60,f71])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f180,plain,
    ( sK1 != k4_xboole_0(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl4_1
    | spl4_2
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f155,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f155,plain,
    ( ~ r1_xboole_0(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl4_1
    | spl4_2
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f105,f95,f112,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ r2_hidden(X2,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f69])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).

fof(f112,plain,
    ( ~ r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f100,f92])).

fof(f92,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f55,f71])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
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

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f100,plain,
    ( sK0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl4_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f95,plain,
    ( r2_hidden(sK0,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_1
  <=> r2_hidden(sK0,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f105,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl4_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f132,plain,
    ( spl4_1
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f119,f77])).

fof(f77,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f45,f70])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f119,plain,
    ( ~ r1_tarski(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))
    | spl4_1
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f104,f96,f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f96,plain,
    ( ~ r2_hidden(sK0,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f104,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f110,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f108,f76])).

fof(f76,plain,(
    ! [X0] : r2_hidden(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f42,f72])).

fof(f72,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f44,f70,f71])).

fof(f44,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f42,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f108,plain,
    ( ~ r2_hidden(sK0,k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))
    | spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f96,f99])).

fof(f99,plain,
    ( sK0 = sK1
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f107,plain,
    ( spl4_1
    | spl4_3
    | spl4_2 ),
    inference(avatar_split_clause,[],[f75,f98,f103,f94])).

fof(f75,plain,
    ( sK0 = sK1
    | r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f39,f72])).

fof(f39,plain,
    ( sK0 = sK1
    | r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ( sK0 != sK1
        & ~ r2_hidden(sK0,sK1) )
      | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
    & ( sK0 = sK1
      | r2_hidden(sK0,sK1)
      | r2_hidden(sK0,k1_ordinal1(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ( ( X0 != X1
            & ~ r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_ordinal1(X1)) )
        & ( X0 = X1
          | r2_hidden(X0,X1)
          | r2_hidden(X0,k1_ordinal1(X1)) ) )
   => ( ( ( sK0 != sK1
          & ~ r2_hidden(sK0,sK1) )
        | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
      & ( sK0 = sK1
        | r2_hidden(sK0,sK1)
        | r2_hidden(sK0,k1_ordinal1(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k1_ordinal1(X1)) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k1_ordinal1(X1)) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <~> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,k1_ordinal1(X1))
      <=> ( X0 = X1
          | r2_hidden(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f106,plain,
    ( ~ spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f74,f103,f94])).

fof(f74,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f40,f72])).

fof(f40,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f101,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f73,f98,f94])).

fof(f73,plain,
    ( sK0 != sK1
    | ~ r2_hidden(sK0,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f41,f72])).

fof(f41,plain,
    ( sK0 != sK1
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n003.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 14:19:57 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.19/0.51  % (29393)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.53  % (29410)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.53  % (29402)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.54  % (29391)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.55  % (29386)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.55  % (29392)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.55  % (29406)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.56  % (29398)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.56  % (29400)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.56  % (29385)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.56  % (29410)Refutation found. Thanks to Tanya!
% 0.19/0.56  % SZS status Theorem for theBenchmark
% 0.19/0.56  % SZS output start Proof for theBenchmark
% 0.19/0.56  fof(f265,plain,(
% 0.19/0.56    $false),
% 0.19/0.56    inference(avatar_sat_refutation,[],[f101,f106,f107,f110,f132,f264])).
% 0.19/0.56  fof(f264,plain,(
% 0.19/0.56    ~spl4_1 | spl4_2 | spl4_3),
% 0.19/0.56    inference(avatar_contradiction_clause,[],[f263])).
% 0.19/0.56  fof(f263,plain,(
% 0.19/0.56    $false | (~spl4_1 | spl4_2 | spl4_3)),
% 0.19/0.56    inference(subsumption_resolution,[],[f255,f89])).
% 0.19/0.56  fof(f89,plain,(
% 0.19/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.56    inference(equality_resolution,[],[f48])).
% 0.19/0.56  fof(f48,plain,(
% 0.19/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.19/0.56    inference(cnf_transformation,[],[f29])).
% 0.19/0.56  fof(f29,plain,(
% 0.19/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.56    inference(flattening,[],[f28])).
% 0.19/0.56  fof(f28,plain,(
% 0.19/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.56    inference(nnf_transformation,[],[f3])).
% 0.19/0.56  fof(f3,axiom,(
% 0.19/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.56  fof(f255,plain,(
% 0.19/0.56    ~r1_tarski(sK1,sK1) | (~spl4_1 | spl4_2 | spl4_3)),
% 0.19/0.56    inference(unit_resulting_resolution,[],[f237,f61])).
% 0.19/0.56  fof(f61,plain,(
% 0.19/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f22])).
% 0.19/0.56  fof(f22,plain,(
% 0.19/0.56    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.19/0.56    inference(ennf_transformation,[],[f15])).
% 0.19/0.56  fof(f15,axiom,(
% 0.19/0.56    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.19/0.56  fof(f237,plain,(
% 0.19/0.56    r2_hidden(sK1,sK1) | (~spl4_1 | spl4_2 | spl4_3)),
% 0.19/0.56    inference(unit_resulting_resolution,[],[f180,f82])).
% 0.19/0.56  fof(f82,plain,(
% 0.19/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.19/0.56    inference(definition_unfolding,[],[f60,f71])).
% 0.19/0.56  fof(f71,plain,(
% 0.19/0.56    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.19/0.56    inference(definition_unfolding,[],[f43,f69])).
% 0.19/0.56  fof(f69,plain,(
% 0.19/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.19/0.56    inference(definition_unfolding,[],[f47,f68])).
% 0.19/0.56  fof(f68,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.19/0.56    inference(definition_unfolding,[],[f62,f67])).
% 0.19/0.56  fof(f67,plain,(
% 0.19/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f10])).
% 0.19/0.56  fof(f10,axiom,(
% 0.19/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.19/0.56  fof(f62,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f9])).
% 0.19/0.56  fof(f9,axiom,(
% 0.19/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.56  fof(f47,plain,(
% 0.19/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f8])).
% 0.19/0.56  fof(f8,axiom,(
% 0.19/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.56  fof(f43,plain,(
% 0.19/0.56    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f7])).
% 0.19/0.56  fof(f7,axiom,(
% 0.19/0.56    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.56  fof(f60,plain,(
% 0.19/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f38])).
% 0.19/0.56  fof(f38,plain,(
% 0.19/0.56    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.19/0.56    inference(nnf_transformation,[],[f12])).
% 0.19/0.56  fof(f12,axiom,(
% 0.19/0.56    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.19/0.56  fof(f180,plain,(
% 0.19/0.56    sK1 != k4_xboole_0(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | (~spl4_1 | spl4_2 | spl4_3)),
% 0.19/0.56    inference(unit_resulting_resolution,[],[f155,f51])).
% 0.19/0.56  fof(f51,plain,(
% 0.19/0.56    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.19/0.56    inference(cnf_transformation,[],[f20])).
% 0.19/0.56  fof(f20,plain,(
% 0.19/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 0.19/0.56    inference(ennf_transformation,[],[f18])).
% 0.19/0.56  fof(f18,plain,(
% 0.19/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 0.19/0.56    inference(unused_predicate_definition_removal,[],[f5])).
% 0.19/0.56  fof(f5,axiom,(
% 0.19/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.19/0.56  fof(f155,plain,(
% 0.19/0.56    ~r1_xboole_0(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | (~spl4_1 | spl4_2 | spl4_3)),
% 0.19/0.56    inference(unit_resulting_resolution,[],[f105,f95,f112,f87])).
% 0.19/0.56  fof(f87,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~r2_hidden(X2,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.56    inference(definition_unfolding,[],[f63,f70])).
% 0.19/0.56  fof(f70,plain,(
% 0.19/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.19/0.56    inference(definition_unfolding,[],[f46,f69])).
% 0.19/0.56  fof(f46,plain,(
% 0.19/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.19/0.56    inference(cnf_transformation,[],[f11])).
% 0.19/0.56  fof(f11,axiom,(
% 0.19/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.19/0.56  fof(f63,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f23])).
% 0.19/0.56  fof(f23,plain,(
% 0.19/0.56    ! [X0,X1,X2] : ((~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.19/0.56    inference(ennf_transformation,[],[f2])).
% 0.19/0.56  fof(f2,axiom,(
% 0.19/0.56    ! [X0,X1,X2] : ~(~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & ~(~r2_hidden(X2,X1) & r2_hidden(X2,X0)) & r2_hidden(X2,k2_xboole_0(X0,X1)) & r1_xboole_0(X0,X1))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).
% 0.19/0.56  fof(f112,plain,(
% 0.19/0.56    ~r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | spl4_2),
% 0.19/0.56    inference(unit_resulting_resolution,[],[f100,f92])).
% 0.19/0.56  fof(f92,plain,(
% 0.19/0.56    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 0.19/0.56    inference(equality_resolution,[],[f81])).
% 0.19/0.56  fof(f81,plain,(
% 0.19/0.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 0.19/0.56    inference(definition_unfolding,[],[f55,f71])).
% 0.19/0.56  fof(f55,plain,(
% 0.19/0.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.19/0.56    inference(cnf_transformation,[],[f37])).
% 0.19/0.56  fof(f37,plain,(
% 0.19/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.19/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 0.19/0.56  fof(f36,plain,(
% 0.19/0.56    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 0.19/0.56    introduced(choice_axiom,[])).
% 0.19/0.56  fof(f35,plain,(
% 0.19/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.19/0.56    inference(rectify,[],[f34])).
% 0.19/0.56  fof(f34,plain,(
% 0.19/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.19/0.56    inference(nnf_transformation,[],[f6])).
% 0.19/0.56  fof(f6,axiom,(
% 0.19/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.19/0.56  fof(f100,plain,(
% 0.19/0.56    sK0 != sK1 | spl4_2),
% 0.19/0.56    inference(avatar_component_clause,[],[f98])).
% 0.19/0.56  fof(f98,plain,(
% 0.19/0.56    spl4_2 <=> sK0 = sK1),
% 0.19/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.56  fof(f95,plain,(
% 0.19/0.56    r2_hidden(sK0,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) | ~spl4_1),
% 0.19/0.56    inference(avatar_component_clause,[],[f94])).
% 0.19/0.56  fof(f94,plain,(
% 0.19/0.56    spl4_1 <=> r2_hidden(sK0,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))),
% 0.19/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.56  fof(f105,plain,(
% 0.19/0.56    ~r2_hidden(sK0,sK1) | spl4_3),
% 0.19/0.56    inference(avatar_component_clause,[],[f103])).
% 0.19/0.56  fof(f103,plain,(
% 0.19/0.56    spl4_3 <=> r2_hidden(sK0,sK1)),
% 0.19/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.19/0.56  fof(f132,plain,(
% 0.19/0.56    spl4_1 | ~spl4_3),
% 0.19/0.56    inference(avatar_contradiction_clause,[],[f131])).
% 0.19/0.56  fof(f131,plain,(
% 0.19/0.56    $false | (spl4_1 | ~spl4_3)),
% 0.19/0.56    inference(subsumption_resolution,[],[f119,f77])).
% 0.19/0.56  fof(f77,plain,(
% 0.19/0.56    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 0.19/0.56    inference(definition_unfolding,[],[f45,f70])).
% 0.19/0.56  fof(f45,plain,(
% 0.19/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.19/0.56    inference(cnf_transformation,[],[f4])).
% 0.19/0.56  fof(f4,axiom,(
% 0.19/0.56    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.19/0.56  fof(f119,plain,(
% 0.19/0.56    ~r1_tarski(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) | (spl4_1 | ~spl4_3)),
% 0.19/0.56    inference(unit_resulting_resolution,[],[f104,f96,f52])).
% 0.19/0.56  fof(f52,plain,(
% 0.19/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f33])).
% 0.19/0.56  fof(f33,plain,(
% 0.19/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 0.19/0.56  fof(f32,plain,(
% 0.19/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.19/0.56    introduced(choice_axiom,[])).
% 0.19/0.56  fof(f31,plain,(
% 0.19/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.56    inference(rectify,[],[f30])).
% 0.19/0.56  fof(f30,plain,(
% 0.19/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.56    inference(nnf_transformation,[],[f21])).
% 0.19/0.56  fof(f21,plain,(
% 0.19/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.19/0.56    inference(ennf_transformation,[],[f1])).
% 0.19/0.56  fof(f1,axiom,(
% 0.19/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.19/0.56  fof(f96,plain,(
% 0.19/0.56    ~r2_hidden(sK0,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) | spl4_1),
% 0.19/0.56    inference(avatar_component_clause,[],[f94])).
% 0.19/0.56  fof(f104,plain,(
% 0.19/0.56    r2_hidden(sK0,sK1) | ~spl4_3),
% 0.19/0.56    inference(avatar_component_clause,[],[f103])).
% 0.19/0.56  fof(f110,plain,(
% 0.19/0.56    spl4_1 | ~spl4_2),
% 0.19/0.56    inference(avatar_contradiction_clause,[],[f109])).
% 0.19/0.56  fof(f109,plain,(
% 0.19/0.56    $false | (spl4_1 | ~spl4_2)),
% 0.19/0.56    inference(subsumption_resolution,[],[f108,f76])).
% 0.19/0.56  fof(f76,plain,(
% 0.19/0.56    ( ! [X0] : (r2_hidden(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0))))) )),
% 0.19/0.56    inference(definition_unfolding,[],[f42,f72])).
% 0.19/0.56  fof(f72,plain,(
% 0.19/0.56    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0)))) )),
% 0.19/0.56    inference(definition_unfolding,[],[f44,f70,f71])).
% 0.19/0.56  fof(f44,plain,(
% 0.19/0.56    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.19/0.56    inference(cnf_transformation,[],[f13])).
% 0.19/0.56  fof(f13,axiom,(
% 0.19/0.56    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.19/0.56  fof(f42,plain,(
% 0.19/0.56    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.19/0.56    inference(cnf_transformation,[],[f14])).
% 0.19/0.56  fof(f14,axiom,(
% 0.19/0.56    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.19/0.56  fof(f108,plain,(
% 0.19/0.56    ~r2_hidden(sK0,k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) | (spl4_1 | ~spl4_2)),
% 0.19/0.56    inference(forward_demodulation,[],[f96,f99])).
% 0.19/0.56  fof(f99,plain,(
% 0.19/0.56    sK0 = sK1 | ~spl4_2),
% 0.19/0.56    inference(avatar_component_clause,[],[f98])).
% 0.19/0.56  fof(f107,plain,(
% 0.19/0.56    spl4_1 | spl4_3 | spl4_2),
% 0.19/0.56    inference(avatar_split_clause,[],[f75,f98,f103,f94])).
% 0.19/0.57  fof(f75,plain,(
% 0.19/0.57    sK0 = sK1 | r2_hidden(sK0,sK1) | r2_hidden(sK0,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))),
% 0.19/0.57    inference(definition_unfolding,[],[f39,f72])).
% 0.19/0.57  fof(f39,plain,(
% 0.19/0.57    sK0 = sK1 | r2_hidden(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.19/0.57    inference(cnf_transformation,[],[f27])).
% 0.19/0.57  fof(f27,plain,(
% 0.19/0.57    ((sK0 != sK1 & ~r2_hidden(sK0,sK1)) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (sK0 = sK1 | r2_hidden(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1)))),
% 0.19/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).
% 0.19/0.57  fof(f26,plain,(
% 0.19/0.57    ? [X0,X1] : (((X0 != X1 & ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))) & (X0 = X1 | r2_hidden(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) => (((sK0 != sK1 & ~r2_hidden(sK0,sK1)) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (sK0 = sK1 | r2_hidden(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))))),
% 0.19/0.57    introduced(choice_axiom,[])).
% 0.19/0.57  fof(f25,plain,(
% 0.19/0.57    ? [X0,X1] : (((X0 != X1 & ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))) & (X0 = X1 | r2_hidden(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))))),
% 0.19/0.57    inference(flattening,[],[f24])).
% 0.19/0.57  fof(f24,plain,(
% 0.19/0.57    ? [X0,X1] : (((X0 != X1 & ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | r2_hidden(X0,k1_ordinal1(X1))))),
% 0.19/0.57    inference(nnf_transformation,[],[f19])).
% 0.19/0.57  fof(f19,plain,(
% 0.19/0.57    ? [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <~> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.19/0.57    inference(ennf_transformation,[],[f17])).
% 0.19/0.57  fof(f17,negated_conjecture,(
% 0.19/0.57    ~! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.19/0.57    inference(negated_conjecture,[],[f16])).
% 0.19/0.57  fof(f16,conjecture,(
% 0.19/0.57    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.19/0.57  fof(f106,plain,(
% 0.19/0.57    ~spl4_1 | ~spl4_3),
% 0.19/0.57    inference(avatar_split_clause,[],[f74,f103,f94])).
% 0.19/0.57  fof(f74,plain,(
% 0.19/0.57    ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))),
% 0.19/0.57    inference(definition_unfolding,[],[f40,f72])).
% 0.19/0.57  fof(f40,plain,(
% 0.19/0.57    ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.19/0.57    inference(cnf_transformation,[],[f27])).
% 0.19/0.57  fof(f101,plain,(
% 0.19/0.57    ~spl4_1 | ~spl4_2),
% 0.19/0.57    inference(avatar_split_clause,[],[f73,f98,f94])).
% 0.19/0.57  fof(f73,plain,(
% 0.19/0.57    sK0 != sK1 | ~r2_hidden(sK0,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))),
% 0.19/0.57    inference(definition_unfolding,[],[f41,f72])).
% 0.19/0.57  fof(f41,plain,(
% 0.19/0.57    sK0 != sK1 | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.19/0.57    inference(cnf_transformation,[],[f27])).
% 0.19/0.57  % SZS output end Proof for theBenchmark
% 0.19/0.57  % (29410)------------------------------
% 0.19/0.57  % (29410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.57  % (29410)Termination reason: Refutation
% 0.19/0.57  
% 0.19/0.57  % (29410)Memory used [KB]: 10874
% 0.19/0.57  % (29410)Time elapsed: 0.135 s
% 0.19/0.57  % (29410)------------------------------
% 0.19/0.57  % (29410)------------------------------
% 0.19/0.57  % (29383)Success in time 0.222 s
%------------------------------------------------------------------------------
