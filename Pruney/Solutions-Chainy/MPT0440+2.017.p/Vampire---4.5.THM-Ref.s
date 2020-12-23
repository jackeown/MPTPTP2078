%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:59 EST 2020

% Result     : Theorem 4.15s
% Output     : Refutation 4.15s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 453 expanded)
%              Number of leaves         :   28 ( 173 expanded)
%              Depth                    :   12
%              Number of atoms          :  427 (1403 expanded)
%              Number of equality atoms :  119 ( 433 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2602,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f82,f143,f144,f234,f354,f355,f364,f369,f379,f1367,f1919,f2412,f2599])).

fof(f2599,plain,
    ( spl9_1
    | ~ spl9_5
    | ~ spl9_15
    | ~ spl9_95 ),
    inference(avatar_contradiction_clause,[],[f2598])).

fof(f2598,plain,
    ( $false
    | spl9_1
    | ~ spl9_5
    | ~ spl9_15
    | ~ spl9_95 ),
    inference(subsumption_resolution,[],[f2597,f72])).

fof(f72,plain,
    ( k1_relat_1(sK2) != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl9_1
  <=> k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f2597,plain,
    ( k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl9_5
    | ~ spl9_15
    | ~ spl9_95 ),
    inference(subsumption_resolution,[],[f2596,f123])).

fof(f123,plain,
    ( ! [X9] : r2_hidden(X9,k2_enumset1(X9,X9,X9,X9))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl9_5
  <=> ! [X9] : r2_hidden(X9,k2_enumset1(X9,X9,X9,X9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f2596,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl9_15
    | ~ spl9_95 ),
    inference(subsumption_resolution,[],[f2593,f368])).

fof(f368,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f366])).

fof(f366,plain,
    ( spl9_15
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f2593,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl9_95 ),
    inference(superposition,[],[f162,f2408])).

fof(f2408,plain,
    ( sK0 = sK6(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl9_95 ),
    inference(avatar_component_clause,[],[f2406])).

fof(f2406,plain,
    ( spl9_95
  <=> sK0 = sK6(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_95])])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),k1_relat_1(X0))
      | ~ r2_hidden(sK6(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(resolution,[],[f44,f66])).

fof(f66,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f22,f25,f24,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
      | k1_relat_1(X0) = X1
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2412,plain,
    ( spl9_95
    | spl9_1
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f2411,f230,f70,f2406])).

fof(f230,plain,
    ( spl9_12
  <=> sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f2411,plain,
    ( sK0 = sK6(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | spl9_1
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f2410,f440])).

fof(f440,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | sK0 = X0 )
    | ~ spl9_12 ),
    inference(superposition,[],[f109,f232])).

fof(f232,plain,
    ( sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f230])).

fof(f109,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(k2_zfmisc_1(k2_enumset1(X4,X4,X4,X4),X5)))
      | X3 = X4 ) ),
    inference(resolution,[],[f62,f66])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
      | X0 = X2 ) ),
    inference(definition_unfolding,[],[f49,f53])).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f2410,plain,
    ( sK0 = sK6(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | r2_hidden(sK6(sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK2))
    | spl9_1
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f2374,f72])).

fof(f2374,plain,
    ( k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
    | sK0 = sK6(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | r2_hidden(sK6(sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK2))
    | ~ spl9_12 ),
    inference(resolution,[],[f1007,f456])).

fof(f456,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl9_12 ),
    inference(superposition,[],[f118,f232])).

fof(f118,plain,(
    ! [X14,X12,X13] :
      ( r2_hidden(X12,k1_relat_1(k2_zfmisc_1(X13,k2_enumset1(X14,X14,X14,X14))))
      | ~ r2_hidden(X12,X13) ) ),
    inference(resolution,[],[f67,f65])).

fof(f65,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
      | ~ r2_hidden(X0,X2) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
      | X1 != X3
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f48,f53])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      | X1 != X3
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f1007,plain,
    ( ! [X0] :
        ( r2_hidden(sK6(sK2,X0),X0)
        | k1_relat_1(sK2) = X0
        | sK0 = sK6(sK2,X0) )
    | ~ spl9_12 ),
    inference(superposition,[],[f211,f232])).

fof(f211,plain,(
    ! [X17,X18,X16] :
      ( r2_hidden(sK6(k2_zfmisc_1(k2_enumset1(X16,X16,X16,X16),X17),X18),X18)
      | k1_relat_1(k2_zfmisc_1(k2_enumset1(X16,X16,X16,X16),X17)) = X18
      | sK6(k2_zfmisc_1(k2_enumset1(X16,X16,X16,X16),X17),X18) = X16 ) ),
    inference(resolution,[],[f43,f62])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
      | k1_relat_1(X0) = X1
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1919,plain,
    ( spl9_2
    | ~ spl9_5
    | ~ spl9_14
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f1891,f1361,f361,f122,f74])).

fof(f74,plain,
    ( spl9_2
  <=> k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f361,plain,
    ( spl9_14
  <=> r2_hidden(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f1361,plain,
    ( spl9_46
  <=> sK1 = sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f1891,plain,
    ( k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl9_5
    | ~ spl9_14
    | ~ spl9_46 ),
    inference(subsumption_resolution,[],[f1890,f123])).

fof(f1890,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl9_14
    | ~ spl9_46 ),
    inference(subsumption_resolution,[],[f1887,f363])).

fof(f363,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f361])).

fof(f1887,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK2))
    | ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl9_46 ),
    inference(superposition,[],[f158,f1363])).

fof(f1363,plain,
    ( sK1 = sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl9_46 ),
    inference(avatar_component_clause,[],[f1361])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),k2_relat_1(X0))
      | ~ r2_hidden(sK3(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(resolution,[],[f40,f64])).

fof(f64,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f16,f19,f18,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
      | k2_relat_1(X0) = X1
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1367,plain,
    ( spl9_46
    | spl9_2
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f1366,f230,f74,f1361])).

fof(f1366,plain,
    ( sK1 = sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl9_2
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f1365,f397])).

fof(f397,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK2))
        | sK1 = X0 )
    | ~ spl9_12 ),
    inference(superposition,[],[f92,f232])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(k2_zfmisc_1(X2,k2_enumset1(X1,X1,X1,X1))))
      | X0 = X1 ) ),
    inference(resolution,[],[f58,f64])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
      | X1 = X3 ) ),
    inference(definition_unfolding,[],[f47,f53])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1365,plain,
    ( sK1 = sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_relat_1(sK2))
    | spl9_2
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f1322,f76])).

fof(f76,plain,
    ( k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f1322,plain,
    ( k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1)
    | sK1 = sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_relat_1(sK2))
    | ~ spl9_12 ),
    inference(resolution,[],[f859,f504])).

fof(f504,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
        | r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl9_12 ),
    inference(superposition,[],[f141,f232])).

fof(f141,plain,(
    ! [X17,X18,X16] :
      ( r2_hidden(X16,k2_relat_1(k2_zfmisc_1(k2_enumset1(X18,X18,X18,X18),X17)))
      | ~ r2_hidden(X16,X17) ) ),
    inference(resolution,[],[f68,f63])).

fof(f63,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
      | ~ r2_hidden(X1,X3) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
      | ~ r2_hidden(X1,X3)
      | X0 != X2 ) ),
    inference(definition_unfolding,[],[f51,f53])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      | ~ r2_hidden(X1,X3)
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f859,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK2,X0),X0)
        | k2_relat_1(sK2) = X0
        | sK1 = sK3(sK2,X0) )
    | ~ spl9_12 ),
    inference(superposition,[],[f194,f232])).

fof(f194,plain,(
    ! [X10,X11,X9] :
      ( r2_hidden(sK3(k2_zfmisc_1(X9,k2_enumset1(X10,X10,X10,X10)),X11),X11)
      | k2_relat_1(k2_zfmisc_1(X9,k2_enumset1(X10,X10,X10,X10))) = X11
      | sK3(k2_zfmisc_1(X9,k2_enumset1(X10,X10,X10,X10)),X11) = X10 ) ),
    inference(resolution,[],[f39,f58])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
      | k2_relat_1(X0) = X1
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f379,plain,
    ( spl9_13
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f374,f122,f79,f252])).

fof(f252,plain,
    ( spl9_13
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f79,plain,
    ( spl9_3
  <=> sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f374,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(superposition,[],[f123,f81])).

fof(f81,plain,
    ( sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f369,plain,
    ( spl9_15
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f329,f252,f366])).

fof(f329,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl9_13 ),
    inference(resolution,[],[f254,f65])).

fof(f254,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f252])).

fof(f364,plain,
    ( spl9_14
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f330,f252,f361])).

fof(f330,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl9_13 ),
    inference(resolution,[],[f254,f63])).

fof(f355,plain,
    ( spl9_1
    | ~ spl9_6
    | ~ spl9_7 ),
    inference(avatar_contradiction_clause,[],[f349])).

fof(f349,plain,
    ( $false
    | spl9_1
    | ~ spl9_6
    | ~ spl9_7 ),
    inference(unit_resulting_resolution,[],[f72,f126,f130,f43])).

fof(f130,plain,
    ( ! [X10] : ~ r2_hidden(X10,sK2)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl9_7
  <=> ! [X10] : ~ r2_hidden(X10,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f126,plain,
    ( ! [X8,X7] : ~ r2_hidden(X7,k2_enumset1(X8,X8,X8,X8))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl9_6
  <=> ! [X7,X8] : ~ r2_hidden(X7,k2_enumset1(X8,X8,X8,X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f354,plain,
    ( spl9_2
    | ~ spl9_6
    | ~ spl9_7 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | spl9_2
    | ~ spl9_6
    | ~ spl9_7 ),
    inference(unit_resulting_resolution,[],[f76,f126,f130,f39])).

fof(f234,plain,
    ( spl9_12
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f221,f79,f230])).

fof(f221,plain,
    ( sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl9_3 ),
    inference(superposition,[],[f81,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) = k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f36,f53,f53,f53])).

fof(f36,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(f144,plain,
    ( spl9_5
    | spl9_7
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f138,f79,f129,f122])).

fof(f138,plain,
    ( ! [X10,X11] :
        ( ~ r2_hidden(X10,sK2)
        | r2_hidden(X11,k2_enumset1(X11,X11,X11,X11)) )
    | ~ spl9_3 ),
    inference(resolution,[],[f68,f99])).

fof(f99,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,sK2))
        | r2_hidden(X0,X2) )
    | ~ spl9_3 ),
    inference(superposition,[],[f59,f81])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f46,f53])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f143,plain,
    ( spl9_5
    | spl9_6 ),
    inference(avatar_split_clause,[],[f136,f125,f122])).

fof(f136,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X5,k2_enumset1(X6,X6,X6,X6))
      | r2_hidden(X7,k2_enumset1(X7,X7,X7,X7)) ) ),
    inference(resolution,[],[f68,f59])).

fof(f82,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f55,f79])).

fof(f55,plain,(
    sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) ),
    inference(definition_unfolding,[],[f32,f53])).

fof(f32,plain,(
    sK2 = k1_tarski(k4_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( k1_tarski(sK1) != k2_relat_1(sK2)
      | k1_tarski(sK0) != k1_relat_1(sK2) )
    & sK2 = k1_tarski(k4_tarski(sK0,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_tarski(X1) != k2_relat_1(X2)
          | k1_tarski(X0) != k1_relat_1(X2) )
        & k1_tarski(k4_tarski(X0,X1)) = X2
        & v1_relat_1(X2) )
   => ( ( k1_tarski(sK1) != k2_relat_1(sK2)
        | k1_tarski(sK0) != k1_relat_1(sK2) )
      & sK2 = k1_tarski(k4_tarski(sK0,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( k1_tarski(X1) != k2_relat_1(X2)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( k1_tarski(X1) != k2_relat_1(X2)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( k1_tarski(k4_tarski(X0,X1)) = X2
         => ( k1_tarski(X1) = k2_relat_1(X2)
            & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).

fof(f77,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f54,f74,f70])).

fof(f54,plain,
    ( k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_relat_1(sK2) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f33,f53,f53])).

fof(f33,plain,
    ( k1_tarski(sK1) != k2_relat_1(sK2)
    | k1_tarski(sK0) != k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:38:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (18122)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (18128)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (18129)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (18130)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (18123)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (18125)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (18123)Refutation not found, incomplete strategy% (18123)------------------------------
% 0.22/0.52  % (18123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (18146)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.52  % (18123)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (18123)Memory used [KB]: 1663
% 0.22/0.52  % (18123)Time elapsed: 0.099 s
% 0.22/0.52  % (18123)------------------------------
% 0.22/0.52  % (18123)------------------------------
% 0.22/0.53  % (18136)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (18140)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (18144)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (18132)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (18139)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (18148)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (18133)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (18145)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (18124)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (18131)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.54  % (18138)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (18150)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (18138)Refutation not found, incomplete strategy% (18138)------------------------------
% 0.22/0.55  % (18138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18138)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18138)Memory used [KB]: 10618
% 0.22/0.55  % (18138)Time elapsed: 0.129 s
% 0.22/0.55  % (18138)------------------------------
% 0.22/0.55  % (18138)------------------------------
% 0.22/0.55  % (18135)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.55  % (18141)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.56  % (18126)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.56  % (18143)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.57  % (18127)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.57  % (18151)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.57  % (18151)Refutation not found, incomplete strategy% (18151)------------------------------
% 0.22/0.57  % (18151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (18151)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (18151)Memory used [KB]: 1663
% 0.22/0.57  % (18151)Time elapsed: 0.002 s
% 0.22/0.57  % (18151)------------------------------
% 0.22/0.57  % (18151)------------------------------
% 0.22/0.58  % (18149)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.58  % (18134)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.58  % (18147)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.64/0.59  % (18142)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.64/0.59  % (18137)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 2.01/0.63  % (18122)Refutation not found, incomplete strategy% (18122)------------------------------
% 2.01/0.63  % (18122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.63  % (18122)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.63  
% 2.01/0.63  % (18122)Memory used [KB]: 1663
% 2.01/0.63  % (18122)Time elapsed: 0.196 s
% 2.01/0.63  % (18122)------------------------------
% 2.01/0.63  % (18122)------------------------------
% 2.01/0.66  % (18125)Refutation not found, incomplete strategy% (18125)------------------------------
% 2.01/0.66  % (18125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.66  % (18125)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.66  
% 2.01/0.66  % (18125)Memory used [KB]: 6140
% 2.01/0.66  % (18125)Time elapsed: 0.237 s
% 2.01/0.66  % (18125)------------------------------
% 2.01/0.66  % (18125)------------------------------
% 2.01/0.68  % (18153)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.01/0.72  % (18154)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.71/0.74  % (18156)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.71/0.76  % (18157)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.71/0.76  % (18155)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.19/0.82  % (18146)Time limit reached!
% 3.19/0.82  % (18146)------------------------------
% 3.19/0.82  % (18146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.19/0.82  % (18146)Termination reason: Time limit
% 3.19/0.82  % (18146)Termination phase: Saturation
% 3.19/0.82  
% 3.19/0.82  % (18146)Memory used [KB]: 13816
% 3.19/0.82  % (18146)Time elapsed: 0.400 s
% 3.19/0.82  % (18146)------------------------------
% 3.19/0.82  % (18146)------------------------------
% 3.19/0.82  % (18124)Time limit reached!
% 3.19/0.82  % (18124)------------------------------
% 3.19/0.82  % (18124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.19/0.82  % (18124)Termination reason: Time limit
% 3.19/0.82  
% 3.19/0.82  % (18124)Memory used [KB]: 7547
% 3.19/0.82  % (18124)Time elapsed: 0.408 s
% 3.19/0.82  % (18124)------------------------------
% 3.19/0.82  % (18124)------------------------------
% 4.15/0.95  % (18136)Time limit reached!
% 4.15/0.95  % (18136)------------------------------
% 4.15/0.95  % (18136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.15/0.95  % (18136)Termination reason: Time limit
% 4.15/0.95  
% 4.15/0.95  % (18136)Memory used [KB]: 5373
% 4.15/0.95  % (18136)Time elapsed: 0.518 s
% 4.15/0.95  % (18136)------------------------------
% 4.15/0.95  % (18136)------------------------------
% 4.15/0.95  % (18128)Time limit reached!
% 4.15/0.95  % (18128)------------------------------
% 4.15/0.95  % (18128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.15/0.95  % (18128)Termination reason: Time limit
% 4.15/0.95  
% 4.15/0.95  % (18128)Memory used [KB]: 15223
% 4.15/0.95  % (18128)Time elapsed: 0.523 s
% 4.15/0.95  % (18128)------------------------------
% 4.15/0.95  % (18128)------------------------------
% 4.15/0.95  % (18154)Refutation found. Thanks to Tanya!
% 4.15/0.95  % SZS status Theorem for theBenchmark
% 4.15/0.95  % SZS output start Proof for theBenchmark
% 4.15/0.95  fof(f2602,plain,(
% 4.15/0.95    $false),
% 4.15/0.95    inference(avatar_sat_refutation,[],[f77,f82,f143,f144,f234,f354,f355,f364,f369,f379,f1367,f1919,f2412,f2599])).
% 4.15/0.95  fof(f2599,plain,(
% 4.15/0.95    spl9_1 | ~spl9_5 | ~spl9_15 | ~spl9_95),
% 4.15/0.95    inference(avatar_contradiction_clause,[],[f2598])).
% 4.15/0.95  fof(f2598,plain,(
% 4.15/0.95    $false | (spl9_1 | ~spl9_5 | ~spl9_15 | ~spl9_95)),
% 4.15/0.95    inference(subsumption_resolution,[],[f2597,f72])).
% 4.15/0.95  fof(f72,plain,(
% 4.15/0.95    k1_relat_1(sK2) != k2_enumset1(sK0,sK0,sK0,sK0) | spl9_1),
% 4.15/0.95    inference(avatar_component_clause,[],[f70])).
% 4.15/0.95  fof(f70,plain,(
% 4.15/0.95    spl9_1 <=> k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 4.15/0.95    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 4.15/0.95  fof(f2597,plain,(
% 4.15/0.95    k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0) | (~spl9_5 | ~spl9_15 | ~spl9_95)),
% 4.15/0.95    inference(subsumption_resolution,[],[f2596,f123])).
% 4.15/0.95  fof(f123,plain,(
% 4.15/0.95    ( ! [X9] : (r2_hidden(X9,k2_enumset1(X9,X9,X9,X9))) ) | ~spl9_5),
% 4.15/0.95    inference(avatar_component_clause,[],[f122])).
% 4.15/0.95  fof(f122,plain,(
% 4.15/0.95    spl9_5 <=> ! [X9] : r2_hidden(X9,k2_enumset1(X9,X9,X9,X9))),
% 4.15/0.95    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 4.15/0.95  fof(f2596,plain,(
% 4.15/0.95    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0) | (~spl9_15 | ~spl9_95)),
% 4.15/0.95    inference(subsumption_resolution,[],[f2593,f368])).
% 4.15/0.95  fof(f368,plain,(
% 4.15/0.95    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl9_15),
% 4.15/0.95    inference(avatar_component_clause,[],[f366])).
% 4.15/0.95  fof(f366,plain,(
% 4.15/0.95    spl9_15 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 4.15/0.95    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 4.15/0.95  fof(f2593,plain,(
% 4.15/0.95    ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl9_95),
% 4.15/0.95    inference(superposition,[],[f162,f2408])).
% 4.15/0.95  fof(f2408,plain,(
% 4.15/0.95    sK0 = sK6(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl9_95),
% 4.15/0.95    inference(avatar_component_clause,[],[f2406])).
% 4.15/0.95  fof(f2406,plain,(
% 4.15/0.95    spl9_95 <=> sK0 = sK6(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 4.15/0.95    introduced(avatar_definition,[new_symbols(naming,[spl9_95])])).
% 4.15/0.95  fof(f162,plain,(
% 4.15/0.95    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),k1_relat_1(X0)) | ~r2_hidden(sK6(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 4.15/0.95    inference(resolution,[],[f44,f66])).
% 4.15/0.95  fof(f66,plain,(
% 4.15/0.95    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 4.15/0.95    inference(equality_resolution,[],[f41])).
% 4.15/0.95  fof(f41,plain,(
% 4.15/0.95    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 4.15/0.95    inference(cnf_transformation,[],[f26])).
% 4.15/0.95  fof(f26,plain,(
% 4.15/0.95    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 4.15/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f22,f25,f24,f23])).
% 4.15/0.95  fof(f23,plain,(
% 4.15/0.95    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 4.15/0.95    introduced(choice_axiom,[])).
% 4.15/0.95  fof(f24,plain,(
% 4.15/0.95    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0))),
% 4.15/0.95    introduced(choice_axiom,[])).
% 4.15/0.95  fof(f25,plain,(
% 4.15/0.95    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0))),
% 4.15/0.95    introduced(choice_axiom,[])).
% 4.15/0.95  fof(f22,plain,(
% 4.15/0.95    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 4.15/0.95    inference(rectify,[],[f21])).
% 4.15/0.95  fof(f21,plain,(
% 4.15/0.95    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 4.15/0.95    inference(nnf_transformation,[],[f7])).
% 4.15/0.95  fof(f7,axiom,(
% 4.15/0.95    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 4.15/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 4.15/0.95  fof(f44,plain,(
% 4.15/0.95    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | k1_relat_1(X0) = X1 | ~r2_hidden(sK6(X0,X1),X1)) )),
% 4.15/0.95    inference(cnf_transformation,[],[f26])).
% 4.15/0.95  fof(f2412,plain,(
% 4.15/0.95    spl9_95 | spl9_1 | ~spl9_12),
% 4.15/0.95    inference(avatar_split_clause,[],[f2411,f230,f70,f2406])).
% 4.15/0.95  fof(f230,plain,(
% 4.15/0.95    spl9_12 <=> sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 4.15/0.95    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 4.15/0.95  fof(f2411,plain,(
% 4.15/0.95    sK0 = sK6(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | (spl9_1 | ~spl9_12)),
% 4.15/0.95    inference(subsumption_resolution,[],[f2410,f440])).
% 4.15/0.95  fof(f440,plain,(
% 4.15/0.95    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | sK0 = X0) ) | ~spl9_12),
% 4.15/0.95    inference(superposition,[],[f109,f232])).
% 4.15/0.95  fof(f232,plain,(
% 4.15/0.95    sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl9_12),
% 4.15/0.95    inference(avatar_component_clause,[],[f230])).
% 4.15/0.95  fof(f109,plain,(
% 4.15/0.95    ( ! [X4,X5,X3] : (~r2_hidden(X3,k1_relat_1(k2_zfmisc_1(k2_enumset1(X4,X4,X4,X4),X5))) | X3 = X4) )),
% 4.15/0.95    inference(resolution,[],[f62,f66])).
% 4.15/0.95  fof(f62,plain,(
% 4.15/0.95    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) | X0 = X2) )),
% 4.15/0.95    inference(definition_unfolding,[],[f49,f53])).
% 4.15/0.95  fof(f53,plain,(
% 4.15/0.95    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 4.15/0.95    inference(definition_unfolding,[],[f34,f52])).
% 4.15/0.95  fof(f52,plain,(
% 4.15/0.95    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 4.15/0.95    inference(definition_unfolding,[],[f35,f45])).
% 4.15/0.95  fof(f45,plain,(
% 4.15/0.95    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 4.15/0.95    inference(cnf_transformation,[],[f3])).
% 4.15/0.95  fof(f3,axiom,(
% 4.15/0.95    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 4.15/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 4.15/0.95  fof(f35,plain,(
% 4.15/0.95    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.15/0.95    inference(cnf_transformation,[],[f2])).
% 4.15/0.95  fof(f2,axiom,(
% 4.15/0.95    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.15/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 4.15/0.95  fof(f34,plain,(
% 4.15/0.95    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 4.15/0.95    inference(cnf_transformation,[],[f1])).
% 4.15/0.95  fof(f1,axiom,(
% 4.15/0.95    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 4.15/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 4.15/0.95  fof(f49,plain,(
% 4.15/0.95    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) )),
% 4.15/0.95    inference(cnf_transformation,[],[f30])).
% 4.15/0.95  fof(f30,plain,(
% 4.15/0.95    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 4.15/0.95    inference(flattening,[],[f29])).
% 4.15/0.95  fof(f29,plain,(
% 4.15/0.95    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | (~r2_hidden(X1,X3) | X0 != X2)) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 4.15/0.95    inference(nnf_transformation,[],[f4])).
% 4.15/0.95  fof(f4,axiom,(
% 4.15/0.95    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 4.15/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).
% 4.15/0.95  fof(f2410,plain,(
% 4.15/0.95    sK0 = sK6(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(sK6(sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK2)) | (spl9_1 | ~spl9_12)),
% 4.15/0.95    inference(subsumption_resolution,[],[f2374,f72])).
% 4.15/0.95  fof(f2374,plain,(
% 4.15/0.95    k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0) | sK0 = sK6(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(sK6(sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK2)) | ~spl9_12),
% 4.15/0.95    inference(resolution,[],[f1007,f456])).
% 4.15/0.95  fof(f456,plain,(
% 4.15/0.95    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(X0,k1_relat_1(sK2))) ) | ~spl9_12),
% 4.15/0.95    inference(superposition,[],[f118,f232])).
% 4.15/0.95  fof(f118,plain,(
% 4.15/0.95    ( ! [X14,X12,X13] : (r2_hidden(X12,k1_relat_1(k2_zfmisc_1(X13,k2_enumset1(X14,X14,X14,X14)))) | ~r2_hidden(X12,X13)) )),
% 4.15/0.95    inference(resolution,[],[f67,f65])).
% 4.15/0.95  fof(f65,plain,(
% 4.15/0.95    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 4.15/0.95    inference(equality_resolution,[],[f42])).
% 4.15/0.95  fof(f42,plain,(
% 4.15/0.95    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 4.15/0.95    inference(cnf_transformation,[],[f26])).
% 4.15/0.95  fof(f67,plain,(
% 4.15/0.95    ( ! [X2,X0,X3] : (r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) | ~r2_hidden(X0,X2)) )),
% 4.15/0.95    inference(equality_resolution,[],[f57])).
% 4.15/0.95  fof(f57,plain,(
% 4.15/0.95    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) | X1 != X3 | ~r2_hidden(X0,X2)) )),
% 4.15/0.95    inference(definition_unfolding,[],[f48,f53])).
% 4.15/0.95  fof(f48,plain,(
% 4.15/0.95    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) )),
% 4.15/0.95    inference(cnf_transformation,[],[f28])).
% 4.15/0.95  fof(f28,plain,(
% 4.15/0.95    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 4.15/0.95    inference(flattening,[],[f27])).
% 4.15/0.95  fof(f27,plain,(
% 4.15/0.95    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | (X1 != X3 | ~r2_hidden(X0,X2))) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 4.15/0.95    inference(nnf_transformation,[],[f5])).
% 4.15/0.95  fof(f5,axiom,(
% 4.15/0.95    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 4.15/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 4.15/0.95  fof(f1007,plain,(
% 4.15/0.95    ( ! [X0] : (r2_hidden(sK6(sK2,X0),X0) | k1_relat_1(sK2) = X0 | sK0 = sK6(sK2,X0)) ) | ~spl9_12),
% 4.15/0.95    inference(superposition,[],[f211,f232])).
% 4.15/0.95  fof(f211,plain,(
% 4.15/0.95    ( ! [X17,X18,X16] : (r2_hidden(sK6(k2_zfmisc_1(k2_enumset1(X16,X16,X16,X16),X17),X18),X18) | k1_relat_1(k2_zfmisc_1(k2_enumset1(X16,X16,X16,X16),X17)) = X18 | sK6(k2_zfmisc_1(k2_enumset1(X16,X16,X16,X16),X17),X18) = X16) )),
% 4.15/0.95    inference(resolution,[],[f43,f62])).
% 4.15/0.95  fof(f43,plain,(
% 4.15/0.95    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | k1_relat_1(X0) = X1 | r2_hidden(sK6(X0,X1),X1)) )),
% 4.15/0.95    inference(cnf_transformation,[],[f26])).
% 4.15/0.95  fof(f1919,plain,(
% 4.15/0.95    spl9_2 | ~spl9_5 | ~spl9_14 | ~spl9_46),
% 4.15/0.95    inference(avatar_split_clause,[],[f1891,f1361,f361,f122,f74])).
% 4.15/0.95  fof(f74,plain,(
% 4.15/0.95    spl9_2 <=> k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1)),
% 4.15/0.95    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 4.15/0.95  fof(f361,plain,(
% 4.15/0.95    spl9_14 <=> r2_hidden(sK1,k2_relat_1(sK2))),
% 4.15/0.95    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 4.15/0.95  fof(f1361,plain,(
% 4.15/0.95    spl9_46 <=> sK1 = sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),
% 4.15/0.95    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).
% 4.15/0.95  fof(f1891,plain,(
% 4.15/0.95    k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1) | (~spl9_5 | ~spl9_14 | ~spl9_46)),
% 4.15/0.95    inference(subsumption_resolution,[],[f1890,f123])).
% 4.15/0.95  fof(f1890,plain,(
% 4.15/0.95    ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1) | (~spl9_14 | ~spl9_46)),
% 4.15/0.95    inference(subsumption_resolution,[],[f1887,f363])).
% 4.15/0.95  fof(f363,plain,(
% 4.15/0.95    r2_hidden(sK1,k2_relat_1(sK2)) | ~spl9_14),
% 4.15/0.95    inference(avatar_component_clause,[],[f361])).
% 4.15/0.95  fof(f1887,plain,(
% 4.15/0.95    ~r2_hidden(sK1,k2_relat_1(sK2)) | ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl9_46),
% 4.15/0.95    inference(superposition,[],[f158,f1363])).
% 4.15/0.95  fof(f1363,plain,(
% 4.15/0.95    sK1 = sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl9_46),
% 4.15/0.95    inference(avatar_component_clause,[],[f1361])).
% 4.15/0.95  fof(f158,plain,(
% 4.15/0.95    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),k2_relat_1(X0)) | ~r2_hidden(sK3(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 4.15/0.95    inference(resolution,[],[f40,f64])).
% 4.15/0.95  fof(f64,plain,(
% 4.15/0.95    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 4.15/0.95    inference(equality_resolution,[],[f37])).
% 4.15/0.95  fof(f37,plain,(
% 4.15/0.95    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 4.15/0.95    inference(cnf_transformation,[],[f20])).
% 4.15/0.95  fof(f20,plain,(
% 4.15/0.95    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 4.15/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f16,f19,f18,f17])).
% 4.15/0.95  fof(f17,plain,(
% 4.15/0.95    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 4.15/0.95    introduced(choice_axiom,[])).
% 4.15/0.95  fof(f18,plain,(
% 4.15/0.95    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0))),
% 4.15/0.95    introduced(choice_axiom,[])).
% 4.15/0.95  fof(f19,plain,(
% 4.15/0.95    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0))),
% 4.15/0.95    introduced(choice_axiom,[])).
% 4.15/0.95  fof(f16,plain,(
% 4.15/0.95    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 4.15/0.95    inference(rectify,[],[f15])).
% 4.15/0.95  fof(f15,plain,(
% 4.15/0.95    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 4.15/0.95    inference(nnf_transformation,[],[f8])).
% 4.15/0.95  fof(f8,axiom,(
% 4.15/0.95    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 4.15/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 4.15/0.95  fof(f40,plain,(
% 4.15/0.95    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | k2_relat_1(X0) = X1 | ~r2_hidden(sK3(X0,X1),X1)) )),
% 4.15/0.95    inference(cnf_transformation,[],[f20])).
% 4.15/0.95  fof(f1367,plain,(
% 4.15/0.95    spl9_46 | spl9_2 | ~spl9_12),
% 4.15/0.95    inference(avatar_split_clause,[],[f1366,f230,f74,f1361])).
% 4.15/0.95  fof(f1366,plain,(
% 4.15/0.95    sK1 = sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | (spl9_2 | ~spl9_12)),
% 4.15/0.95    inference(subsumption_resolution,[],[f1365,f397])).
% 4.15/0.95  fof(f397,plain,(
% 4.15/0.95    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | sK1 = X0) ) | ~spl9_12),
% 4.15/0.95    inference(superposition,[],[f92,f232])).
% 4.15/0.95  fof(f92,plain,(
% 4.15/0.95    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_relat_1(k2_zfmisc_1(X2,k2_enumset1(X1,X1,X1,X1)))) | X0 = X1) )),
% 4.15/0.95    inference(resolution,[],[f58,f64])).
% 4.15/0.95  fof(f58,plain,(
% 4.15/0.95    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) | X1 = X3) )),
% 4.15/0.95    inference(definition_unfolding,[],[f47,f53])).
% 4.15/0.95  fof(f47,plain,(
% 4.15/0.95    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 4.15/0.95    inference(cnf_transformation,[],[f28])).
% 4.15/0.95  fof(f1365,plain,(
% 4.15/0.95    sK1 = sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | r2_hidden(sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_relat_1(sK2)) | (spl9_2 | ~spl9_12)),
% 4.15/0.95    inference(subsumption_resolution,[],[f1322,f76])).
% 4.15/0.95  fof(f76,plain,(
% 4.15/0.95    k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1) | spl9_2),
% 4.15/0.95    inference(avatar_component_clause,[],[f74])).
% 4.15/0.95  fof(f1322,plain,(
% 4.15/0.95    k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1) | sK1 = sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | r2_hidden(sK3(sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_relat_1(sK2)) | ~spl9_12),
% 4.15/0.95    inference(resolution,[],[f859,f504])).
% 4.15/0.95  fof(f504,plain,(
% 4.15/0.95    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) | r2_hidden(X0,k2_relat_1(sK2))) ) | ~spl9_12),
% 4.15/0.95    inference(superposition,[],[f141,f232])).
% 4.15/0.95  fof(f141,plain,(
% 4.15/0.95    ( ! [X17,X18,X16] : (r2_hidden(X16,k2_relat_1(k2_zfmisc_1(k2_enumset1(X18,X18,X18,X18),X17))) | ~r2_hidden(X16,X17)) )),
% 4.15/0.95    inference(resolution,[],[f68,f63])).
% 4.15/0.95  fof(f63,plain,(
% 4.15/0.95    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X6,X5),X0) | r2_hidden(X5,k2_relat_1(X0))) )),
% 4.15/0.95    inference(equality_resolution,[],[f38])).
% 4.15/0.95  fof(f38,plain,(
% 4.15/0.95    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 4.15/0.95    inference(cnf_transformation,[],[f20])).
% 4.15/0.95  fof(f68,plain,(
% 4.15/0.95    ( ! [X2,X3,X1] : (r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) | ~r2_hidden(X1,X3)) )),
% 4.15/0.95    inference(equality_resolution,[],[f60])).
% 4.15/0.95  fof(f60,plain,(
% 4.15/0.95    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) )),
% 4.15/0.95    inference(definition_unfolding,[],[f51,f53])).
% 4.15/0.95  fof(f51,plain,(
% 4.15/0.95    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) )),
% 4.15/0.95    inference(cnf_transformation,[],[f30])).
% 4.15/0.95  fof(f859,plain,(
% 4.15/0.95    ( ! [X0] : (r2_hidden(sK3(sK2,X0),X0) | k2_relat_1(sK2) = X0 | sK1 = sK3(sK2,X0)) ) | ~spl9_12),
% 4.15/0.95    inference(superposition,[],[f194,f232])).
% 4.15/0.95  fof(f194,plain,(
% 4.15/0.95    ( ! [X10,X11,X9] : (r2_hidden(sK3(k2_zfmisc_1(X9,k2_enumset1(X10,X10,X10,X10)),X11),X11) | k2_relat_1(k2_zfmisc_1(X9,k2_enumset1(X10,X10,X10,X10))) = X11 | sK3(k2_zfmisc_1(X9,k2_enumset1(X10,X10,X10,X10)),X11) = X10) )),
% 4.15/0.95    inference(resolution,[],[f39,f58])).
% 4.15/0.95  fof(f39,plain,(
% 4.15/0.95    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | k2_relat_1(X0) = X1 | r2_hidden(sK3(X0,X1),X1)) )),
% 4.15/0.95    inference(cnf_transformation,[],[f20])).
% 4.15/0.95  fof(f379,plain,(
% 4.15/0.95    spl9_13 | ~spl9_3 | ~spl9_5),
% 4.15/0.95    inference(avatar_split_clause,[],[f374,f122,f79,f252])).
% 4.15/0.95  fof(f252,plain,(
% 4.15/0.95    spl9_13 <=> r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 4.15/0.95    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 4.15/0.95  fof(f79,plain,(
% 4.15/0.95    spl9_3 <=> sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),
% 4.15/0.95    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 4.15/0.95  fof(f374,plain,(
% 4.15/0.95    r2_hidden(k4_tarski(sK0,sK1),sK2) | (~spl9_3 | ~spl9_5)),
% 4.15/0.95    inference(superposition,[],[f123,f81])).
% 4.15/0.95  fof(f81,plain,(
% 4.15/0.95    sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) | ~spl9_3),
% 4.15/0.95    inference(avatar_component_clause,[],[f79])).
% 4.15/0.95  fof(f369,plain,(
% 4.15/0.95    spl9_15 | ~spl9_13),
% 4.15/0.95    inference(avatar_split_clause,[],[f329,f252,f366])).
% 4.15/0.95  fof(f329,plain,(
% 4.15/0.95    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl9_13),
% 4.15/0.95    inference(resolution,[],[f254,f65])).
% 4.15/0.95  fof(f254,plain,(
% 4.15/0.95    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl9_13),
% 4.15/0.95    inference(avatar_component_clause,[],[f252])).
% 4.15/0.95  fof(f364,plain,(
% 4.15/0.95    spl9_14 | ~spl9_13),
% 4.15/0.95    inference(avatar_split_clause,[],[f330,f252,f361])).
% 4.15/0.95  fof(f330,plain,(
% 4.15/0.95    r2_hidden(sK1,k2_relat_1(sK2)) | ~spl9_13),
% 4.15/0.95    inference(resolution,[],[f254,f63])).
% 4.15/0.95  fof(f355,plain,(
% 4.15/0.95    spl9_1 | ~spl9_6 | ~spl9_7),
% 4.15/0.95    inference(avatar_contradiction_clause,[],[f349])).
% 4.15/0.95  fof(f349,plain,(
% 4.15/0.95    $false | (spl9_1 | ~spl9_6 | ~spl9_7)),
% 4.15/0.95    inference(unit_resulting_resolution,[],[f72,f126,f130,f43])).
% 4.15/0.95  fof(f130,plain,(
% 4.15/0.95    ( ! [X10] : (~r2_hidden(X10,sK2)) ) | ~spl9_7),
% 4.15/0.95    inference(avatar_component_clause,[],[f129])).
% 4.15/0.95  fof(f129,plain,(
% 4.15/0.95    spl9_7 <=> ! [X10] : ~r2_hidden(X10,sK2)),
% 4.15/0.95    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 4.15/0.95  fof(f126,plain,(
% 4.15/0.95    ( ! [X8,X7] : (~r2_hidden(X7,k2_enumset1(X8,X8,X8,X8))) ) | ~spl9_6),
% 4.15/0.95    inference(avatar_component_clause,[],[f125])).
% 4.15/0.95  fof(f125,plain,(
% 4.15/0.95    spl9_6 <=> ! [X7,X8] : ~r2_hidden(X7,k2_enumset1(X8,X8,X8,X8))),
% 4.15/0.95    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 4.15/0.95  fof(f354,plain,(
% 4.15/0.95    spl9_2 | ~spl9_6 | ~spl9_7),
% 4.15/0.95    inference(avatar_contradiction_clause,[],[f348])).
% 4.15/0.95  fof(f348,plain,(
% 4.15/0.95    $false | (spl9_2 | ~spl9_6 | ~spl9_7)),
% 4.15/0.95    inference(unit_resulting_resolution,[],[f76,f126,f130,f39])).
% 4.15/0.95  fof(f234,plain,(
% 4.15/0.95    spl9_12 | ~spl9_3),
% 4.15/0.95    inference(avatar_split_clause,[],[f221,f79,f230])).
% 4.15/0.95  fof(f221,plain,(
% 4.15/0.95    sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl9_3),
% 4.15/0.95    inference(superposition,[],[f81,f56])).
% 4.15/0.95  fof(f56,plain,(
% 4.15/0.95    ( ! [X0,X1] : (k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) = k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))) )),
% 4.15/0.95    inference(definition_unfolding,[],[f36,f53,f53,f53])).
% 4.15/0.95  fof(f36,plain,(
% 4.15/0.95    ( ! [X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))) )),
% 4.15/0.95    inference(cnf_transformation,[],[f6])).
% 4.15/0.95  fof(f6,axiom,(
% 4.15/0.95    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))),
% 4.15/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).
% 4.15/0.95  fof(f144,plain,(
% 4.15/0.95    spl9_5 | spl9_7 | ~spl9_3),
% 4.15/0.95    inference(avatar_split_clause,[],[f138,f79,f129,f122])).
% 4.15/0.95  fof(f138,plain,(
% 4.15/0.95    ( ! [X10,X11] : (~r2_hidden(X10,sK2) | r2_hidden(X11,k2_enumset1(X11,X11,X11,X11))) ) | ~spl9_3),
% 4.15/0.95    inference(resolution,[],[f68,f99])).
% 4.15/0.95  fof(f99,plain,(
% 4.15/0.95    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,sK2)) | r2_hidden(X0,X2)) ) | ~spl9_3),
% 4.15/0.95    inference(superposition,[],[f59,f81])).
% 4.15/0.95  fof(f59,plain,(
% 4.15/0.95    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) | r2_hidden(X0,X2)) )),
% 4.15/0.95    inference(definition_unfolding,[],[f46,f53])).
% 4.15/0.95  fof(f46,plain,(
% 4.15/0.95    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 4.15/0.95    inference(cnf_transformation,[],[f28])).
% 4.15/0.95  fof(f143,plain,(
% 4.15/0.95    spl9_5 | spl9_6),
% 4.15/0.95    inference(avatar_split_clause,[],[f136,f125,f122])).
% 4.15/0.95  fof(f136,plain,(
% 4.15/0.95    ( ! [X6,X7,X5] : (~r2_hidden(X5,k2_enumset1(X6,X6,X6,X6)) | r2_hidden(X7,k2_enumset1(X7,X7,X7,X7))) )),
% 4.15/0.95    inference(resolution,[],[f68,f59])).
% 4.15/0.95  fof(f82,plain,(
% 4.15/0.95    spl9_3),
% 4.15/0.95    inference(avatar_split_clause,[],[f55,f79])).
% 4.15/0.95  fof(f55,plain,(
% 4.15/0.95    sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),
% 4.15/0.95    inference(definition_unfolding,[],[f32,f53])).
% 4.15/0.95  fof(f32,plain,(
% 4.15/0.95    sK2 = k1_tarski(k4_tarski(sK0,sK1))),
% 4.15/0.95    inference(cnf_transformation,[],[f14])).
% 4.15/0.95  fof(f14,plain,(
% 4.15/0.95    (k1_tarski(sK1) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2)) & sK2 = k1_tarski(k4_tarski(sK0,sK1)) & v1_relat_1(sK2)),
% 4.15/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 4.15/0.95  fof(f13,plain,(
% 4.15/0.95    ? [X0,X1,X2] : ((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2 & v1_relat_1(X2)) => ((k1_tarski(sK1) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2)) & sK2 = k1_tarski(k4_tarski(sK0,sK1)) & v1_relat_1(sK2))),
% 4.15/0.95    introduced(choice_axiom,[])).
% 4.15/0.95  fof(f12,plain,(
% 4.15/0.95    ? [X0,X1,X2] : ((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2 & v1_relat_1(X2))),
% 4.15/0.95    inference(flattening,[],[f11])).
% 4.15/0.95  fof(f11,plain,(
% 4.15/0.95    ? [X0,X1,X2] : (((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2) & v1_relat_1(X2))),
% 4.15/0.95    inference(ennf_transformation,[],[f10])).
% 4.15/0.95  fof(f10,negated_conjecture,(
% 4.15/0.95    ~! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 4.15/0.95    inference(negated_conjecture,[],[f9])).
% 4.15/0.95  fof(f9,conjecture,(
% 4.15/0.95    ! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 4.15/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).
% 4.15/0.95  fof(f77,plain,(
% 4.15/0.95    ~spl9_1 | ~spl9_2),
% 4.15/0.95    inference(avatar_split_clause,[],[f54,f74,f70])).
% 4.15/0.95  fof(f54,plain,(
% 4.15/0.95    k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1) | k1_relat_1(sK2) != k2_enumset1(sK0,sK0,sK0,sK0)),
% 4.15/0.95    inference(definition_unfolding,[],[f33,f53,f53])).
% 4.15/0.95  fof(f33,plain,(
% 4.15/0.95    k1_tarski(sK1) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2)),
% 4.15/0.95    inference(cnf_transformation,[],[f14])).
% 4.15/0.95  % SZS output end Proof for theBenchmark
% 4.15/0.95  % (18154)------------------------------
% 4.15/0.95  % (18154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.15/0.95  % (18154)Termination reason: Refutation
% 4.15/0.95  
% 4.15/0.95  % (18154)Memory used [KB]: 12665
% 4.15/0.95  % (18154)Time elapsed: 0.349 s
% 4.15/0.95  % (18154)------------------------------
% 4.15/0.95  % (18154)------------------------------
% 4.15/0.96  % (18121)Success in time 0.584 s
%------------------------------------------------------------------------------
