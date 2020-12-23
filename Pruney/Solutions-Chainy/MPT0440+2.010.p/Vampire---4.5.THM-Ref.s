%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:58 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 247 expanded)
%              Number of leaves         :   18 (  92 expanded)
%              Depth                    :   12
%              Number of atoms          :  237 ( 455 expanded)
%              Number of equality atoms :   99 ( 260 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f799,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f73,f94,f101,f106,f215,f278,f398,f491,f798])).

fof(f798,plain,
    ( ~ spl10_7
    | spl10_4
    | ~ spl10_15 ),
    inference(avatar_split_clause,[],[f796,f395,f70,f103])).

fof(f103,plain,
    ( spl10_7
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f70,plain,
    ( spl10_4
  <=> k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f395,plain,
    ( spl10_15
  <=> sK0 = sK9(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f796,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl10_4
    | ~ spl10_15 ),
    inference(trivial_inequality_removal,[],[f795])).

fof(f795,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | k1_relat_1(sK2) != k1_relat_1(sK2)
    | sK0 != sK0
    | spl10_4
    | ~ spl10_15 ),
    inference(superposition,[],[f418,f397])).

fof(f397,plain,
    ( sK0 = sK9(sK0,k1_relat_1(sK2))
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f395])).

fof(f418,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK9(sK0,X1),X1)
        | k1_relat_1(sK2) != X1
        | sK0 != sK9(sK0,X1) )
    | spl10_4 ),
    inference(superposition,[],[f72,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = X1
      | ~ r2_hidden(sK9(X0,X1),X1)
      | sK9(X0,X1) != X0 ) ),
    inference(definition_unfolding,[],[f30,f36])).

fof(f36,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f16,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f17,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f17,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f16,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( sK9(X0,X1) != X0
      | ~ r2_hidden(sK9(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f72,plain,
    ( k1_relat_1(sK2) != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl10_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f491,plain,
    ( ~ spl10_6
    | spl10_3
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f489,f275,f66,f98])).

fof(f98,plain,
    ( spl10_6
  <=> r2_hidden(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f66,plain,
    ( spl10_3
  <=> k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f275,plain,
    ( spl10_11
  <=> sK1 = sK9(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f489,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK2))
    | spl10_3
    | ~ spl10_11 ),
    inference(trivial_inequality_removal,[],[f488])).

fof(f488,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK2))
    | k2_relat_1(sK2) != k2_relat_1(sK2)
    | sK1 != sK1
    | spl10_3
    | ~ spl10_11 ),
    inference(superposition,[],[f320,f277])).

fof(f277,plain,
    ( sK1 = sK9(sK1,k2_relat_1(sK2))
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f275])).

fof(f320,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK9(sK1,X1),X1)
        | k2_relat_1(sK2) != X1
        | sK1 != sK9(sK1,X1) )
    | spl10_3 ),
    inference(superposition,[],[f68,f40])).

fof(f68,plain,
    ( k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1)
    | spl10_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f398,plain,
    ( spl10_15
    | spl10_4
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f392,f194,f70,f395])).

fof(f194,plain,
    ( spl10_10
  <=> sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f392,plain,
    ( sK0 = sK9(sK0,k1_relat_1(sK2))
    | spl10_4
    | ~ spl10_10 ),
    inference(trivial_inequality_removal,[],[f391])).

fof(f391,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | sK0 = sK9(sK0,k1_relat_1(sK2))
    | spl10_4
    | ~ spl10_10 ),
    inference(duplicate_literal_removal,[],[f387])).

fof(f387,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | sK0 = sK9(sK0,k1_relat_1(sK2))
    | sK0 = sK9(sK0,k1_relat_1(sK2))
    | spl10_4
    | ~ spl10_10 ),
    inference(resolution,[],[f293,f229])).

fof(f229,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relat_1(sK2))
        | sK0 = X3 )
    | ~ spl10_10 ),
    inference(resolution,[],[f222,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f222,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | sK0 = X0 )
    | ~ spl10_10 ),
    inference(superposition,[],[f46,f196])).

fof(f196,plain,
    ( sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f194])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
      | X0 = X2 ) ),
    inference(definition_unfolding,[],[f32,f36])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f293,plain,
    ( ! [X0] :
        ( r2_hidden(sK9(sK0,X0),X0)
        | k1_relat_1(sK2) != X0
        | sK0 = sK9(sK0,X0) )
    | spl10_4 ),
    inference(superposition,[],[f72,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = X1
      | r2_hidden(sK9(X0,X1),X1)
      | sK9(X0,X1) = X0 ) ),
    inference(definition_unfolding,[],[f29,f36])).

fof(f29,plain,(
    ! [X0,X1] :
      ( sK9(X0,X1) = X0
      | r2_hidden(sK9(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f278,plain,
    ( spl10_11
    | spl10_3
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f272,f194,f66,f275])).

fof(f272,plain,
    ( sK1 = sK9(sK1,k2_relat_1(sK2))
    | spl10_3
    | ~ spl10_10 ),
    inference(trivial_inequality_removal,[],[f271])).

fof(f271,plain,
    ( sK1 = sK9(sK1,k2_relat_1(sK2))
    | k2_relat_1(sK2) != k2_relat_1(sK2)
    | spl10_3
    | ~ spl10_10 ),
    inference(duplicate_literal_removal,[],[f270])).

fof(f270,plain,
    ( sK1 = sK9(sK1,k2_relat_1(sK2))
    | k2_relat_1(sK2) != k2_relat_1(sK2)
    | sK1 = sK9(sK1,k2_relat_1(sK2))
    | spl10_3
    | ~ spl10_10 ),
    inference(resolution,[],[f261,f74])).

fof(f74,plain,
    ( ! [X0] :
        ( r2_hidden(sK9(sK1,X0),X0)
        | k2_relat_1(sK2) != X0
        | sK1 = sK9(sK1,X0) )
    | spl10_3 ),
    inference(superposition,[],[f68,f41])).

fof(f261,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relat_1(sK2))
        | sK1 = X3 )
    | ~ spl10_10 ),
    inference(resolution,[],[f248,f49])).

fof(f49,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK7(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f248,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | sK1 = X1 )
    | ~ spl10_10 ),
    inference(resolution,[],[f223,f51])).

fof(f51,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f28,f36])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f223,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X3,k2_enumset1(sK1,sK1,sK1,sK1))
        | ~ r2_hidden(k4_tarski(X2,X3),sK2) )
    | ~ spl10_10 ),
    inference(superposition,[],[f45,f196])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
      | r2_hidden(X1,X3) ) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f215,plain,
    ( spl10_10
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f82,f61,f194])).

fof(f61,plain,
    ( spl10_2
  <=> sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f82,plain,
    ( sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl10_2 ),
    inference(superposition,[],[f39,f63])).

fof(f63,plain,
    ( sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f39,plain,(
    ! [X0,X1] : k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) = k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f18,f36,f36,f36])).

fof(f18,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(f106,plain,
    ( spl10_7
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f96,f91,f103])).

fof(f91,plain,
    ( spl10_5
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f96,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl10_5 ),
    inference(resolution,[],[f93,f48])).

fof(f48,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f93,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f101,plain,
    ( spl10_6
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f95,f91,f98])).

fof(f95,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl10_5 ),
    inference(resolution,[],[f93,f50])).

fof(f50,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f94,plain,
    ( spl10_5
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f88,f61,f91])).

fof(f88,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl10_2 ),
    inference(superposition,[],[f53,f63])).

fof(f53,plain,(
    ! [X2] : r2_hidden(X2,k2_enumset1(X2,X2,X2,X2)) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k2_enumset1(X2,X2,X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f27,f36])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f73,plain,
    ( ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f38,f70,f66])).

fof(f38,plain,
    ( k1_relat_1(sK2) != k2_enumset1(sK0,sK0,sK0,sK0)
    | k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f13,f36,f36])).

fof(f13,plain,
    ( k1_tarski(sK0) != k1_relat_1(sK2)
    | k1_tarski(sK1) != k2_relat_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

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

fof(f64,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f37,f61])).

fof(f37,plain,(
    sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) ),
    inference(definition_unfolding,[],[f15,f36])).

fof(f15,plain,(
    sK2 = k1_tarski(k4_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:15:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.47  % (5991)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.47  % (5992)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.51  % (5986)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.51  % (5987)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.51  % (6003)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.19/0.51  % (6001)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.19/0.51  % (6001)Refutation not found, incomplete strategy% (6001)------------------------------
% 0.19/0.51  % (6001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (6001)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (6001)Memory used [KB]: 10618
% 0.19/0.51  % (6001)Time elapsed: 0.103 s
% 0.19/0.51  % (6001)------------------------------
% 0.19/0.51  % (6001)------------------------------
% 0.19/0.52  % (5994)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.52  % (5996)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.52  % (5988)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.53  % (5999)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.53  % (6011)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.53  % (5997)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.53  % (6009)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.19/0.53  % (6010)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.19/0.53  % (5985)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.53  % (6012)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.53  % (6013)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.53  % (6006)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.19/0.54  % (6005)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.54  % (6002)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.19/0.54  % (6004)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.54  % (6008)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.54  % (5998)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.55  % (5984)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.55  % (6014)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.55  % (6007)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.55  % (6000)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.56  % (5990)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.56  % (5993)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.58  % (5995)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.58  % (6014)Refutation not found, incomplete strategy% (6014)------------------------------
% 0.19/0.58  % (6014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.58  % (6014)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.58  
% 0.19/0.58  % (6014)Memory used [KB]: 1663
% 0.19/0.58  % (6014)Time elapsed: 0.173 s
% 0.19/0.58  % (6014)------------------------------
% 0.19/0.58  % (6014)------------------------------
% 0.19/0.59  % (6013)Refutation found. Thanks to Tanya!
% 0.19/0.59  % SZS status Theorem for theBenchmark
% 0.19/0.59  % SZS output start Proof for theBenchmark
% 0.19/0.59  fof(f799,plain,(
% 0.19/0.59    $false),
% 0.19/0.59    inference(avatar_sat_refutation,[],[f64,f73,f94,f101,f106,f215,f278,f398,f491,f798])).
% 0.19/0.59  fof(f798,plain,(
% 0.19/0.59    ~spl10_7 | spl10_4 | ~spl10_15),
% 0.19/0.59    inference(avatar_split_clause,[],[f796,f395,f70,f103])).
% 0.19/0.59  fof(f103,plain,(
% 0.19/0.59    spl10_7 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.19/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.19/0.59  fof(f70,plain,(
% 0.19/0.59    spl10_4 <=> k1_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.19/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.19/0.59  fof(f395,plain,(
% 0.19/0.59    spl10_15 <=> sK0 = sK9(sK0,k1_relat_1(sK2))),
% 0.19/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 0.19/0.59  fof(f796,plain,(
% 0.19/0.59    ~r2_hidden(sK0,k1_relat_1(sK2)) | (spl10_4 | ~spl10_15)),
% 0.19/0.59    inference(trivial_inequality_removal,[],[f795])).
% 0.19/0.59  fof(f795,plain,(
% 0.19/0.59    ~r2_hidden(sK0,k1_relat_1(sK2)) | k1_relat_1(sK2) != k1_relat_1(sK2) | sK0 != sK0 | (spl10_4 | ~spl10_15)),
% 0.19/0.59    inference(superposition,[],[f418,f397])).
% 0.19/0.59  fof(f397,plain,(
% 0.19/0.59    sK0 = sK9(sK0,k1_relat_1(sK2)) | ~spl10_15),
% 0.19/0.59    inference(avatar_component_clause,[],[f395])).
% 0.19/0.59  fof(f418,plain,(
% 0.19/0.59    ( ! [X1] : (~r2_hidden(sK9(sK0,X1),X1) | k1_relat_1(sK2) != X1 | sK0 != sK9(sK0,X1)) ) | spl10_4),
% 0.19/0.59    inference(superposition,[],[f72,f40])).
% 0.19/0.59  fof(f40,plain,(
% 0.19/0.59    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = X1 | ~r2_hidden(sK9(X0,X1),X1) | sK9(X0,X1) != X0) )),
% 0.19/0.59    inference(definition_unfolding,[],[f30,f36])).
% 0.19/0.59  fof(f36,plain,(
% 0.19/0.59    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.19/0.59    inference(definition_unfolding,[],[f16,f35])).
% 0.19/0.59  fof(f35,plain,(
% 0.19/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.19/0.59    inference(definition_unfolding,[],[f17,f31])).
% 0.19/0.59  fof(f31,plain,(
% 0.19/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.19/0.59    inference(cnf_transformation,[],[f4])).
% 0.19/0.59  fof(f4,axiom,(
% 0.19/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.19/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.59  fof(f17,plain,(
% 0.19/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.59    inference(cnf_transformation,[],[f3])).
% 0.19/0.59  fof(f3,axiom,(
% 0.19/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.59  fof(f16,plain,(
% 0.19/0.59    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.19/0.59    inference(cnf_transformation,[],[f2])).
% 0.19/0.59  fof(f2,axiom,(
% 0.19/0.59    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.19/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.59  fof(f30,plain,(
% 0.19/0.59    ( ! [X0,X1] : (sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 0.19/0.59    inference(cnf_transformation,[],[f1])).
% 0.19/0.59  fof(f1,axiom,(
% 0.19/0.59    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.19/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.19/0.59  fof(f72,plain,(
% 0.19/0.59    k1_relat_1(sK2) != k2_enumset1(sK0,sK0,sK0,sK0) | spl10_4),
% 0.19/0.59    inference(avatar_component_clause,[],[f70])).
% 0.19/0.59  fof(f491,plain,(
% 0.19/0.59    ~spl10_6 | spl10_3 | ~spl10_11),
% 0.19/0.59    inference(avatar_split_clause,[],[f489,f275,f66,f98])).
% 0.19/0.59  fof(f98,plain,(
% 0.19/0.59    spl10_6 <=> r2_hidden(sK1,k2_relat_1(sK2))),
% 0.19/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.19/0.59  fof(f66,plain,(
% 0.19/0.59    spl10_3 <=> k2_relat_1(sK2) = k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.19/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.19/0.59  fof(f275,plain,(
% 0.19/0.59    spl10_11 <=> sK1 = sK9(sK1,k2_relat_1(sK2))),
% 0.19/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.19/0.59  fof(f489,plain,(
% 0.19/0.59    ~r2_hidden(sK1,k2_relat_1(sK2)) | (spl10_3 | ~spl10_11)),
% 0.19/0.59    inference(trivial_inequality_removal,[],[f488])).
% 0.19/0.59  fof(f488,plain,(
% 0.19/0.59    ~r2_hidden(sK1,k2_relat_1(sK2)) | k2_relat_1(sK2) != k2_relat_1(sK2) | sK1 != sK1 | (spl10_3 | ~spl10_11)),
% 0.19/0.59    inference(superposition,[],[f320,f277])).
% 0.19/0.59  fof(f277,plain,(
% 0.19/0.59    sK1 = sK9(sK1,k2_relat_1(sK2)) | ~spl10_11),
% 0.19/0.59    inference(avatar_component_clause,[],[f275])).
% 0.19/0.59  fof(f320,plain,(
% 0.19/0.59    ( ! [X1] : (~r2_hidden(sK9(sK1,X1),X1) | k2_relat_1(sK2) != X1 | sK1 != sK9(sK1,X1)) ) | spl10_3),
% 0.19/0.59    inference(superposition,[],[f68,f40])).
% 0.19/0.59  fof(f68,plain,(
% 0.19/0.59    k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1) | spl10_3),
% 0.19/0.59    inference(avatar_component_clause,[],[f66])).
% 0.19/0.59  fof(f398,plain,(
% 0.19/0.59    spl10_15 | spl10_4 | ~spl10_10),
% 0.19/0.59    inference(avatar_split_clause,[],[f392,f194,f70,f395])).
% 0.19/0.59  fof(f194,plain,(
% 0.19/0.59    spl10_10 <=> sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.19/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.19/0.59  fof(f392,plain,(
% 0.19/0.59    sK0 = sK9(sK0,k1_relat_1(sK2)) | (spl10_4 | ~spl10_10)),
% 0.19/0.59    inference(trivial_inequality_removal,[],[f391])).
% 0.19/0.59  fof(f391,plain,(
% 0.19/0.59    k1_relat_1(sK2) != k1_relat_1(sK2) | sK0 = sK9(sK0,k1_relat_1(sK2)) | (spl10_4 | ~spl10_10)),
% 0.19/0.59    inference(duplicate_literal_removal,[],[f387])).
% 0.19/0.59  fof(f387,plain,(
% 0.19/0.59    k1_relat_1(sK2) != k1_relat_1(sK2) | sK0 = sK9(sK0,k1_relat_1(sK2)) | sK0 = sK9(sK0,k1_relat_1(sK2)) | (spl10_4 | ~spl10_10)),
% 0.19/0.59    inference(resolution,[],[f293,f229])).
% 0.19/0.59  fof(f229,plain,(
% 0.19/0.59    ( ! [X3] : (~r2_hidden(X3,k1_relat_1(sK2)) | sK0 = X3) ) | ~spl10_10),
% 0.19/0.59    inference(resolution,[],[f222,f47])).
% 0.19/0.59  fof(f47,plain,(
% 0.19/0.59    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 0.19/0.59    inference(equality_resolution,[],[f20])).
% 0.19/0.59  fof(f20,plain,(
% 0.19/0.59    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.19/0.59    inference(cnf_transformation,[],[f7])).
% 0.19/0.59  fof(f7,axiom,(
% 0.19/0.59    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.19/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.19/0.59  fof(f222,plain,(
% 0.19/0.59    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK0 = X0) ) | ~spl10_10),
% 0.19/0.59    inference(superposition,[],[f46,f196])).
% 0.19/0.59  fof(f196,plain,(
% 0.19/0.59    sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl10_10),
% 0.19/0.59    inference(avatar_component_clause,[],[f194])).
% 0.19/0.59  fof(f46,plain,(
% 0.19/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) | X0 = X2) )),
% 0.19/0.59    inference(definition_unfolding,[],[f32,f36])).
% 0.19/0.59  fof(f32,plain,(
% 0.19/0.59    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) )),
% 0.19/0.59    inference(cnf_transformation,[],[f5])).
% 0.19/0.59  fof(f5,axiom,(
% 0.19/0.59    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 0.19/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).
% 0.19/0.59  fof(f293,plain,(
% 0.19/0.59    ( ! [X0] : (r2_hidden(sK9(sK0,X0),X0) | k1_relat_1(sK2) != X0 | sK0 = sK9(sK0,X0)) ) | spl10_4),
% 0.19/0.59    inference(superposition,[],[f72,f41])).
% 0.19/0.59  fof(f41,plain,(
% 0.19/0.59    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = X1 | r2_hidden(sK9(X0,X1),X1) | sK9(X0,X1) = X0) )),
% 0.19/0.59    inference(definition_unfolding,[],[f29,f36])).
% 0.19/0.59  fof(f29,plain,(
% 0.19/0.59    ( ! [X0,X1] : (sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 0.19/0.59    inference(cnf_transformation,[],[f1])).
% 0.19/0.59  fof(f278,plain,(
% 0.19/0.59    spl10_11 | spl10_3 | ~spl10_10),
% 0.19/0.59    inference(avatar_split_clause,[],[f272,f194,f66,f275])).
% 0.19/0.59  fof(f272,plain,(
% 0.19/0.59    sK1 = sK9(sK1,k2_relat_1(sK2)) | (spl10_3 | ~spl10_10)),
% 0.19/0.59    inference(trivial_inequality_removal,[],[f271])).
% 0.19/0.59  fof(f271,plain,(
% 0.19/0.59    sK1 = sK9(sK1,k2_relat_1(sK2)) | k2_relat_1(sK2) != k2_relat_1(sK2) | (spl10_3 | ~spl10_10)),
% 0.19/0.59    inference(duplicate_literal_removal,[],[f270])).
% 0.19/0.59  fof(f270,plain,(
% 0.19/0.59    sK1 = sK9(sK1,k2_relat_1(sK2)) | k2_relat_1(sK2) != k2_relat_1(sK2) | sK1 = sK9(sK1,k2_relat_1(sK2)) | (spl10_3 | ~spl10_10)),
% 0.19/0.59    inference(resolution,[],[f261,f74])).
% 0.19/0.59  fof(f74,plain,(
% 0.19/0.59    ( ! [X0] : (r2_hidden(sK9(sK1,X0),X0) | k2_relat_1(sK2) != X0 | sK1 = sK9(sK1,X0)) ) | spl10_3),
% 0.19/0.59    inference(superposition,[],[f68,f41])).
% 0.19/0.59  fof(f261,plain,(
% 0.19/0.59    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(sK2)) | sK1 = X3) ) | ~spl10_10),
% 0.19/0.59    inference(resolution,[],[f248,f49])).
% 0.19/0.59  fof(f49,plain,(
% 0.19/0.59    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK7(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.19/0.59    inference(equality_resolution,[],[f24])).
% 0.19/0.59  fof(f24,plain,(
% 0.19/0.59    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK7(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.19/0.59    inference(cnf_transformation,[],[f8])).
% 0.19/0.59  fof(f8,axiom,(
% 0.19/0.59    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.19/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.19/0.59  fof(f248,plain,(
% 0.19/0.59    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK1 = X1) ) | ~spl10_10),
% 0.19/0.59    inference(resolution,[],[f223,f51])).
% 0.19/0.59  fof(f51,plain,(
% 0.19/0.59    ( ! [X2,X0] : (~r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) | X0 = X2) )),
% 0.19/0.59    inference(equality_resolution,[],[f42])).
% 0.19/0.59  fof(f42,plain,(
% 0.19/0.59    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.19/0.59    inference(definition_unfolding,[],[f28,f36])).
% 0.19/0.59  fof(f28,plain,(
% 0.19/0.59    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.19/0.59    inference(cnf_transformation,[],[f1])).
% 0.19/0.59  fof(f223,plain,(
% 0.19/0.59    ( ! [X2,X3] : (r2_hidden(X3,k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(k4_tarski(X2,X3),sK2)) ) | ~spl10_10),
% 0.19/0.59    inference(superposition,[],[f45,f196])).
% 0.19/0.59  fof(f45,plain,(
% 0.19/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) | r2_hidden(X1,X3)) )),
% 0.19/0.59    inference(definition_unfolding,[],[f33,f36])).
% 0.19/0.59  fof(f33,plain,(
% 0.19/0.59    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) )),
% 0.19/0.59    inference(cnf_transformation,[],[f5])).
% 0.19/0.59  fof(f215,plain,(
% 0.19/0.59    spl10_10 | ~spl10_2),
% 0.19/0.59    inference(avatar_split_clause,[],[f82,f61,f194])).
% 0.19/0.59  fof(f61,plain,(
% 0.19/0.59    spl10_2 <=> sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),
% 0.19/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.19/0.59  fof(f82,plain,(
% 0.19/0.59    sK2 = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl10_2),
% 0.19/0.59    inference(superposition,[],[f39,f63])).
% 0.19/0.59  fof(f63,plain,(
% 0.19/0.59    sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) | ~spl10_2),
% 0.19/0.59    inference(avatar_component_clause,[],[f61])).
% 0.19/0.59  fof(f39,plain,(
% 0.19/0.59    ( ! [X0,X1] : (k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) = k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))) )),
% 0.19/0.59    inference(definition_unfolding,[],[f18,f36,f36,f36])).
% 0.19/0.59  fof(f18,plain,(
% 0.19/0.59    ( ! [X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))) )),
% 0.19/0.59    inference(cnf_transformation,[],[f6])).
% 0.19/0.59  fof(f6,axiom,(
% 0.19/0.59    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))),
% 0.19/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).
% 0.19/0.59  fof(f106,plain,(
% 0.19/0.59    spl10_7 | ~spl10_5),
% 0.19/0.59    inference(avatar_split_clause,[],[f96,f91,f103])).
% 0.19/0.59  fof(f91,plain,(
% 0.19/0.59    spl10_5 <=> r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.19/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.19/0.59  fof(f96,plain,(
% 0.19/0.59    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl10_5),
% 0.19/0.59    inference(resolution,[],[f93,f48])).
% 0.19/0.59  fof(f48,plain,(
% 0.19/0.59    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 0.19/0.59    inference(equality_resolution,[],[f19])).
% 0.19/0.59  fof(f19,plain,(
% 0.19/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.19/0.59    inference(cnf_transformation,[],[f7])).
% 0.19/0.59  fof(f93,plain,(
% 0.19/0.59    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl10_5),
% 0.19/0.59    inference(avatar_component_clause,[],[f91])).
% 0.19/0.59  fof(f101,plain,(
% 0.19/0.59    spl10_6 | ~spl10_5),
% 0.19/0.59    inference(avatar_split_clause,[],[f95,f91,f98])).
% 0.19/0.59  fof(f95,plain,(
% 0.19/0.59    r2_hidden(sK1,k2_relat_1(sK2)) | ~spl10_5),
% 0.19/0.59    inference(resolution,[],[f93,f50])).
% 0.19/0.59  fof(f50,plain,(
% 0.19/0.59    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 0.19/0.59    inference(equality_resolution,[],[f23])).
% 0.19/0.59  fof(f23,plain,(
% 0.19/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.19/0.59    inference(cnf_transformation,[],[f8])).
% 0.19/0.59  fof(f94,plain,(
% 0.19/0.59    spl10_5 | ~spl10_2),
% 0.19/0.59    inference(avatar_split_clause,[],[f88,f61,f91])).
% 0.19/0.59  fof(f88,plain,(
% 0.19/0.59    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl10_2),
% 0.19/0.59    inference(superposition,[],[f53,f63])).
% 0.19/0.59  fof(f53,plain,(
% 0.19/0.59    ( ! [X2] : (r2_hidden(X2,k2_enumset1(X2,X2,X2,X2))) )),
% 0.19/0.59    inference(equality_resolution,[],[f52])).
% 0.19/0.59  fof(f52,plain,(
% 0.19/0.59    ( ! [X2,X1] : (r2_hidden(X2,X1) | k2_enumset1(X2,X2,X2,X2) != X1) )),
% 0.19/0.59    inference(equality_resolution,[],[f43])).
% 0.19/0.59  fof(f43,plain,(
% 0.19/0.59    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.19/0.59    inference(definition_unfolding,[],[f27,f36])).
% 0.19/0.59  fof(f27,plain,(
% 0.19/0.59    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.19/0.59    inference(cnf_transformation,[],[f1])).
% 0.19/0.59  fof(f73,plain,(
% 0.19/0.59    ~spl10_3 | ~spl10_4),
% 0.19/0.59    inference(avatar_split_clause,[],[f38,f70,f66])).
% 0.19/0.59  fof(f38,plain,(
% 0.19/0.59    k1_relat_1(sK2) != k2_enumset1(sK0,sK0,sK0,sK0) | k2_relat_1(sK2) != k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.19/0.59    inference(definition_unfolding,[],[f13,f36,f36])).
% 0.19/0.59  fof(f13,plain,(
% 0.19/0.59    k1_tarski(sK0) != k1_relat_1(sK2) | k1_tarski(sK1) != k2_relat_1(sK2)),
% 0.19/0.59    inference(cnf_transformation,[],[f12])).
% 0.19/0.59  fof(f12,plain,(
% 0.19/0.59    ? [X0,X1,X2] : ((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2 & v1_relat_1(X2))),
% 0.19/0.59    inference(flattening,[],[f11])).
% 0.19/0.59  fof(f11,plain,(
% 0.19/0.59    ? [X0,X1,X2] : (((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2) & v1_relat_1(X2))),
% 0.19/0.59    inference(ennf_transformation,[],[f10])).
% 0.19/0.59  fof(f10,negated_conjecture,(
% 0.19/0.59    ~! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 0.19/0.59    inference(negated_conjecture,[],[f9])).
% 0.19/0.59  fof(f9,conjecture,(
% 0.19/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 0.19/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).
% 0.19/0.59  fof(f64,plain,(
% 0.19/0.59    spl10_2),
% 0.19/0.59    inference(avatar_split_clause,[],[f37,f61])).
% 0.19/0.59  fof(f37,plain,(
% 0.19/0.59    sK2 = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),
% 0.19/0.59    inference(definition_unfolding,[],[f15,f36])).
% 0.19/0.59  fof(f15,plain,(
% 0.19/0.59    sK2 = k1_tarski(k4_tarski(sK0,sK1))),
% 0.19/0.59    inference(cnf_transformation,[],[f12])).
% 0.19/0.59  % SZS output end Proof for theBenchmark
% 0.19/0.59  % (6013)------------------------------
% 0.19/0.59  % (6013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.59  % (6013)Termination reason: Refutation
% 0.19/0.59  
% 0.19/0.59  % (6013)Memory used [KB]: 11129
% 0.19/0.59  % (6013)Time elapsed: 0.195 s
% 0.19/0.59  % (6013)------------------------------
% 0.19/0.59  % (6013)------------------------------
% 0.19/0.59  % (5983)Success in time 0.235 s
%------------------------------------------------------------------------------
