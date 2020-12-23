%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 195 expanded)
%              Number of leaves         :   32 (  83 expanded)
%              Depth                    :   10
%              Number of atoms          :  345 ( 670 expanded)
%              Number of equality atoms :   43 ( 102 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f391,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f76,f80,f85,f97,f115,f121,f143,f148,f322,f358,f362,f372,f388,f390])).

fof(f390,plain,
    ( sK2 != k1_relset_1(sK2,sK1,sK3)
    | k1_relset_1(sK2,sK1,sK3) != k1_relat_1(sK3)
    | sK2 = k1_relat_1(sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f388,plain,
    ( ~ spl11_1
    | ~ spl11_3
    | ~ spl11_10 ),
    inference(avatar_contradiction_clause,[],[f387])).

fof(f387,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f386,f75])).

fof(f75,plain,
    ( r2_hidden(sK4,sK2)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl11_3
  <=> r2_hidden(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f386,plain,
    ( ~ r2_hidden(sK4,sK2)
    | ~ spl11_1
    | ~ spl11_10 ),
    inference(forward_demodulation,[],[f381,f133])).

fof(f133,plain,
    ( sK2 = k1_relat_1(sK3)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl11_10
  <=> sK2 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f381,plain,
    ( ~ r2_hidden(sK4,k1_relat_1(sK3))
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f61,f66,f49])).

fof(f49,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f30,f33,f32,f31])).

fof(f31,plain,(
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

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f66,plain,
    ( ! [X4] : ~ r2_hidden(k4_tarski(sK4,X4),sK3)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl11_1
  <=> ! [X4] : ~ r2_hidden(k4_tarski(sK4,X4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f61,plain,(
    ! [X0] : sP0(X0,k1_relat_1(X0)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f5,f17])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f372,plain,
    ( spl11_2
    | ~ spl11_10
    | ~ spl11_23 ),
    inference(avatar_split_clause,[],[f369,f319,f131,f68])).

fof(f68,plain,
    ( spl11_2
  <=> sK2 = k1_relset_1(sK2,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f319,plain,
    ( spl11_23
  <=> k1_relset_1(sK2,sK1,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).

fof(f369,plain,
    ( sK2 = k1_relset_1(sK2,sK1,sK3)
    | ~ spl11_10
    | ~ spl11_23 ),
    inference(backward_demodulation,[],[f321,f133])).

fof(f321,plain,
    ( k1_relset_1(sK2,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl11_23 ),
    inference(avatar_component_clause,[],[f319])).

fof(f362,plain,
    ( spl11_9
    | spl11_10
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f339,f118,f131,f127])).

fof(f127,plain,
    ( spl11_9
  <=> r2_xboole_0(k1_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f118,plain,
    ( spl11_8
  <=> r1_tarski(k1_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f339,plain,
    ( sK2 = k1_relat_1(sK3)
    | r2_xboole_0(k1_relat_1(sK3),sK2)
    | ~ spl11_8 ),
    inference(resolution,[],[f120,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f120,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f358,plain,
    ( ~ spl11_4
    | ~ spl11_11
    | spl11_12 ),
    inference(avatar_contradiction_clause,[],[f357])).

fof(f357,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_11
    | spl11_12 ),
    inference(subsumption_resolution,[],[f353,f147])).

fof(f147,plain,
    ( ~ r2_hidden(sK9(k1_relat_1(sK3),sK2),k1_relat_1(sK3))
    | spl11_12 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl11_12
  <=> r2_hidden(sK9(k1_relat_1(sK3),sK2),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f353,plain,
    ( r2_hidden(sK9(k1_relat_1(sK3),sK2),k1_relat_1(sK3))
    | ~ spl11_4
    | ~ spl11_11 ),
    inference(unit_resulting_resolution,[],[f61,f142,f227])).

fof(f227,plain,
    ( ! [X0,X1] :
        ( ~ sP0(sK3,X0)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,sK2) )
    | ~ spl11_4 ),
    inference(resolution,[],[f63,f100])).

fof(f100,plain,
    ( ! [X0] :
        ( sP10(X0,sK3)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl11_4 ),
    inference(resolution,[],[f62,f79])).

fof(f79,plain,
    ( ! [X5] :
        ( r2_hidden(k4_tarski(X5,sK5(X5)),sK3)
        | ~ r2_hidden(X5,sK2) )
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl11_4
  <=> ! [X5] :
        ( r2_hidden(k4_tarski(X5,sK5(X5)),sK3)
        | ~ r2_hidden(X5,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f62,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | sP10(X5,X0) ) ),
    inference(cnf_transformation,[],[f62_D])).

fof(f62_D,plain,(
    ! [X0,X5] :
      ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0)
    <=> ~ sP10(X5,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).

fof(f63,plain,(
    ! [X0,X5,X1] :
      ( ~ sP10(X5,X0)
      | ~ sP0(X0,X1)
      | r2_hidden(X5,X1) ) ),
    inference(general_splitting,[],[f50,f62_D])).

fof(f50,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f142,plain,
    ( r2_hidden(sK9(k1_relat_1(sK3),sK2),sK2)
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl11_11
  <=> r2_hidden(sK9(k1_relat_1(sK3),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f322,plain,
    ( spl11_23
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f304,f82,f319])).

fof(f82,plain,
    ( spl11_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f304,plain,
    ( k1_relset_1(sK2,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl11_5 ),
    inference(unit_resulting_resolution,[],[f84,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f84,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f148,plain,
    ( ~ spl11_12
    | ~ spl11_9 ),
    inference(avatar_split_clause,[],[f135,f127,f145])).

fof(f135,plain,
    ( ~ r2_hidden(sK9(k1_relat_1(sK3),sK2),k1_relat_1(sK3))
    | ~ spl11_9 ),
    inference(unit_resulting_resolution,[],[f129,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK9(X0,X1),X0)
        & r2_hidden(sK9(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f14,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK9(X0,X1),X0)
        & r2_hidden(sK9(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f129,plain,
    ( r2_xboole_0(k1_relat_1(sK3),sK2)
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f143,plain,
    ( spl11_11
    | ~ spl11_9 ),
    inference(avatar_split_clause,[],[f136,f127,f140])).

fof(f136,plain,
    ( r2_hidden(sK9(k1_relat_1(sK3),sK2),sK2)
    | ~ spl11_9 ),
    inference(unit_resulting_resolution,[],[f129,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f121,plain,
    ( spl11_8
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f116,f111,f92,f118])).

fof(f92,plain,
    ( spl11_6
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f111,plain,
    ( spl11_7
  <=> v4_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f116,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(unit_resulting_resolution,[],[f94,f113,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f113,plain,
    ( v4_relat_1(sK3,sK2)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f94,plain,
    ( v1_relat_1(sK3)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f115,plain,
    ( spl11_7
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f109,f82,f111])).

fof(f109,plain,
    ( v4_relat_1(sK3,sK2)
    | ~ spl11_5 ),
    inference(resolution,[],[f58,f84])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f97,plain,
    ( spl11_6
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f96,f82,f92])).

fof(f96,plain,
    ( v1_relat_1(sK3)
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f90,f43])).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f90,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
    | ~ spl11_5 ),
    inference(resolution,[],[f42,f84])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f85,plain,(
    spl11_5 ),
    inference(avatar_split_clause,[],[f38,f82])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( sK2 != k1_relset_1(sK2,sK1,sK3)
      | ( ! [X4] : ~ r2_hidden(k4_tarski(sK4,X4),sK3)
        & r2_hidden(sK4,sK2) ) )
    & ( sK2 = k1_relset_1(sK2,sK1,sK3)
      | ! [X5] :
          ( r2_hidden(k4_tarski(X5,sK5(X5)),sK3)
          | ~ r2_hidden(X5,sK2) ) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f21,f24,f23,f22])).

% (27748)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X1,X0,X2) != X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) ) )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ! [X5] :
              ( ? [X6] : r2_hidden(k4_tarski(X5,X6),X2)
              | ~ r2_hidden(X5,X1) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( sK2 != k1_relset_1(sK2,sK1,sK3)
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),sK3)
            & r2_hidden(X3,sK2) ) )
      & ( sK2 = k1_relset_1(sK2,sK1,sK3)
        | ! [X5] :
            ( ? [X6] : r2_hidden(k4_tarski(X5,X6),sK3)
            | ~ r2_hidden(X5,sK2) ) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3] :
        ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),sK3)
        & r2_hidden(X3,sK2) )
   => ( ! [X4] : ~ r2_hidden(k4_tarski(sK4,X4),sK3)
      & r2_hidden(sK4,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X5] :
      ( ? [X6] : r2_hidden(k4_tarski(X5,X6),sK3)
     => r2_hidden(k4_tarski(X5,sK5(X5)),sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
            & r2_hidden(X3,X1) ) )
      & ( k1_relset_1(X1,X0,X2) = X1
        | ! [X5] :
            ( ? [X6] : r2_hidden(k4_tarski(X5,X6),X2)
            | ~ r2_hidden(X5,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
            & r2_hidden(X3,X1) ) )
      & ( k1_relset_1(X1,X0,X2) = X1
        | ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
            & r2_hidden(X3,X1) ) )
      & ( k1_relset_1(X1,X0,X2) = X1
        | ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <~> k1_relset_1(X1,X0,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( ! [X3] :
              ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
                & r2_hidden(X3,X1) )
        <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

fof(f80,plain,
    ( spl11_4
    | spl11_2 ),
    inference(avatar_split_clause,[],[f39,f68,f78])).

fof(f39,plain,(
    ! [X5] :
      ( sK2 = k1_relset_1(sK2,sK1,sK3)
      | r2_hidden(k4_tarski(X5,sK5(X5)),sK3)
      | ~ r2_hidden(X5,sK2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,
    ( spl11_3
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f40,f68,f73])).

fof(f40,plain,
    ( sK2 != k1_relset_1(sK2,sK1,sK3)
    | r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f71,plain,
    ( spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f41,f68,f65])).

fof(f41,plain,(
    ! [X4] :
      ( sK2 != k1_relset_1(sK2,sK1,sK3)
      | ~ r2_hidden(k4_tarski(sK4,X4),sK3) ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (27747)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.46  % (27759)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.46  % (27753)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.47  % (27755)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (27761)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.48  % (27757)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (27759)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (27750)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (27749)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (27746)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (27743)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f391,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f71,f76,f80,f85,f97,f115,f121,f143,f148,f322,f358,f362,f372,f388,f390])).
% 0.20/0.49  fof(f390,plain,(
% 0.20/0.49    sK2 != k1_relset_1(sK2,sK1,sK3) | k1_relset_1(sK2,sK1,sK3) != k1_relat_1(sK3) | sK2 = k1_relat_1(sK3)),
% 0.20/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.49  fof(f388,plain,(
% 0.20/0.49    ~spl11_1 | ~spl11_3 | ~spl11_10),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f387])).
% 0.20/0.49  fof(f387,plain,(
% 0.20/0.49    $false | (~spl11_1 | ~spl11_3 | ~spl11_10)),
% 0.20/0.49    inference(subsumption_resolution,[],[f386,f75])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    r2_hidden(sK4,sK2) | ~spl11_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f73])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    spl11_3 <=> r2_hidden(sK4,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 0.20/0.49  fof(f386,plain,(
% 0.20/0.49    ~r2_hidden(sK4,sK2) | (~spl11_1 | ~spl11_10)),
% 0.20/0.49    inference(forward_demodulation,[],[f381,f133])).
% 0.20/0.49  fof(f133,plain,(
% 0.20/0.49    sK2 = k1_relat_1(sK3) | ~spl11_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f131])).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    spl11_10 <=> sK2 = k1_relat_1(sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 0.20/0.49  fof(f381,plain,(
% 0.20/0.49    ~r2_hidden(sK4,k1_relat_1(sK3)) | ~spl11_1),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f61,f66,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1) | ~sP0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f30,f33,f32,f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 0.20/0.49    inference(rectify,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    ( ! [X4] : (~r2_hidden(k4_tarski(sK4,X4),sK3)) ) | ~spl11_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f65])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    spl11_1 <=> ! [X4] : ~r2_hidden(k4_tarski(sK4,X4),sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ( ! [X0] : (sP0(X0,k1_relat_1(X0))) )),
% 0.20/0.49    inference(equality_resolution,[],[f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X0,X1] : (sP0(X0,X1) | k1_relat_1(X0) != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k1_relat_1(X0) != X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> sP0(X0,X1))),
% 0.20/0.49    inference(definition_folding,[],[f5,f17])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.20/0.49  fof(f372,plain,(
% 0.20/0.49    spl11_2 | ~spl11_10 | ~spl11_23),
% 0.20/0.49    inference(avatar_split_clause,[],[f369,f319,f131,f68])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    spl11_2 <=> sK2 = k1_relset_1(sK2,sK1,sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 0.20/0.49  fof(f319,plain,(
% 0.20/0.49    spl11_23 <=> k1_relset_1(sK2,sK1,sK3) = k1_relat_1(sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).
% 0.20/0.49  fof(f369,plain,(
% 0.20/0.49    sK2 = k1_relset_1(sK2,sK1,sK3) | (~spl11_10 | ~spl11_23)),
% 0.20/0.49    inference(backward_demodulation,[],[f321,f133])).
% 0.20/0.49  fof(f321,plain,(
% 0.20/0.49    k1_relset_1(sK2,sK1,sK3) = k1_relat_1(sK3) | ~spl11_23),
% 0.20/0.49    inference(avatar_component_clause,[],[f319])).
% 0.20/0.49  fof(f362,plain,(
% 0.20/0.49    spl11_9 | spl11_10 | ~spl11_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f339,f118,f131,f127])).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    spl11_9 <=> r2_xboole_0(k1_relat_1(sK3),sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    spl11_8 <=> r1_tarski(k1_relat_1(sK3),sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 0.20/0.49  fof(f339,plain,(
% 0.20/0.49    sK2 = k1_relat_1(sK3) | r2_xboole_0(k1_relat_1(sK3),sK2) | ~spl11_8),
% 0.20/0.49    inference(resolution,[],[f120,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.20/0.49    inference(flattening,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    r1_tarski(k1_relat_1(sK3),sK2) | ~spl11_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f118])).
% 0.20/0.49  fof(f358,plain,(
% 0.20/0.49    ~spl11_4 | ~spl11_11 | spl11_12),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f357])).
% 0.20/0.49  fof(f357,plain,(
% 0.20/0.49    $false | (~spl11_4 | ~spl11_11 | spl11_12)),
% 0.20/0.49    inference(subsumption_resolution,[],[f353,f147])).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    ~r2_hidden(sK9(k1_relat_1(sK3),sK2),k1_relat_1(sK3)) | spl11_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f145])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    spl11_12 <=> r2_hidden(sK9(k1_relat_1(sK3),sK2),k1_relat_1(sK3))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 0.20/0.49  fof(f353,plain,(
% 0.20/0.49    r2_hidden(sK9(k1_relat_1(sK3),sK2),k1_relat_1(sK3)) | (~spl11_4 | ~spl11_11)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f61,f142,f227])).
% 0.20/0.49  fof(f227,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~sP0(sK3,X0) | r2_hidden(X1,X0) | ~r2_hidden(X1,sK2)) ) | ~spl11_4),
% 0.20/0.49    inference(resolution,[],[f63,f100])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    ( ! [X0] : (sP10(X0,sK3) | ~r2_hidden(X0,sK2)) ) | ~spl11_4),
% 0.20/0.49    inference(resolution,[],[f62,f79])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    ( ! [X5] : (r2_hidden(k4_tarski(X5,sK5(X5)),sK3) | ~r2_hidden(X5,sK2)) ) | ~spl11_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f78])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    spl11_4 <=> ! [X5] : (r2_hidden(k4_tarski(X5,sK5(X5)),sK3) | ~r2_hidden(X5,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | sP10(X5,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f62_D])).
% 0.20/0.49  fof(f62_D,plain,(
% 0.20/0.49    ( ! [X0,X5] : (( ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0) ) <=> ~sP10(X5,X0)) )),
% 0.20/0.49    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X0,X5,X1] : (~sP10(X5,X0) | ~sP0(X0,X1) | r2_hidden(X5,X1)) )),
% 0.20/0.49    inference(general_splitting,[],[f50,f62_D])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~sP0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f34])).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    r2_hidden(sK9(k1_relat_1(sK3),sK2),sK2) | ~spl11_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f140])).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    spl11_11 <=> r2_hidden(sK9(k1_relat_1(sK3),sK2),sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 0.20/0.49  fof(f322,plain,(
% 0.20/0.49    spl11_23 | ~spl11_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f304,f82,f319])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    spl11_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 0.20/0.49  fof(f304,plain,(
% 0.20/0.49    k1_relset_1(sK2,sK1,sK3) = k1_relat_1(sK3) | ~spl11_5),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f84,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl11_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f82])).
% 0.20/0.49  fof(f148,plain,(
% 0.20/0.49    ~spl11_12 | ~spl11_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f135,f127,f145])).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    ~r2_hidden(sK9(k1_relat_1(sK3),sK2),k1_relat_1(sK3)) | ~spl11_9),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f129,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(sK9(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ! [X0,X1] : ((~r2_hidden(sK9(X0,X1),X0) & r2_hidden(sK9(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f14,f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK9(X0,X1),X0) & r2_hidden(sK9(X0,X1),X1)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    r2_xboole_0(k1_relat_1(sK3),sK2) | ~spl11_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f127])).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    spl11_11 | ~spl11_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f136,f127,f140])).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    r2_hidden(sK9(k1_relat_1(sK3),sK2),sK2) | ~spl11_9),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f129,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    spl11_8 | ~spl11_6 | ~spl11_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f116,f111,f92,f118])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    spl11_6 <=> v1_relat_1(sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    spl11_7 <=> v4_relat_1(sK3,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    r1_tarski(k1_relat_1(sK3),sK2) | (~spl11_6 | ~spl11_7)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f94,f113,f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    v4_relat_1(sK3,sK2) | ~spl11_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f111])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    v1_relat_1(sK3) | ~spl11_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f92])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    spl11_7 | ~spl11_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f109,f82,f111])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    v4_relat_1(sK3,sK2) | ~spl11_5),
% 0.20/0.49    inference(resolution,[],[f58,f84])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    spl11_6 | ~spl11_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f96,f82,f92])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    v1_relat_1(sK3) | ~spl11_5),
% 0.20/0.49    inference(subsumption_resolution,[],[f90,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK2,sK1)) | ~spl11_5),
% 0.20/0.49    inference(resolution,[],[f42,f84])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    spl11_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f38,f82])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    (sK2 != k1_relset_1(sK2,sK1,sK3) | (! [X4] : ~r2_hidden(k4_tarski(sK4,X4),sK3) & r2_hidden(sK4,sK2))) & (sK2 = k1_relset_1(sK2,sK1,sK3) | ! [X5] : (r2_hidden(k4_tarski(X5,sK5(X5)),sK3) | ~r2_hidden(X5,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f21,f24,f23,f22])).
% 0.20/0.49  % (27748)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1))) & (k1_relset_1(X1,X0,X2) = X1 | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(X5,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((sK2 != k1_relset_1(sK2,sK1,sK3) | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),sK3) & r2_hidden(X3,sK2))) & (sK2 = k1_relset_1(sK2,sK1,sK3) | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X5,X6),sK3) | ~r2_hidden(X5,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),sK3) & r2_hidden(X3,sK2)) => (! [X4] : ~r2_hidden(k4_tarski(sK4,X4),sK3) & r2_hidden(sK4,sK2))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X5] : (? [X6] : r2_hidden(k4_tarski(X5,X6),sK3) => r2_hidden(k4_tarski(X5,sK5(X5)),sK3))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1))) & (k1_relset_1(X1,X0,X2) = X1 | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(X5,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.49    inference(rectify,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1))) & (k1_relset_1(X1,X0,X2) = X1 | ! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.49    inference(flattening,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (((k1_relset_1(X1,X0,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1))) & (k1_relset_1(X1,X0,X2) = X1 | ! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.49    inference(nnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <~> k1_relset_1(X1,X0,X2) = X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.20/0.49    inference(negated_conjecture,[],[f9])).
% 0.20/0.49  fof(f9,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    spl11_4 | spl11_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f39,f68,f78])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X5] : (sK2 = k1_relset_1(sK2,sK1,sK3) | r2_hidden(k4_tarski(X5,sK5(X5)),sK3) | ~r2_hidden(X5,sK2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    spl11_3 | ~spl11_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f40,f68,f73])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    sK2 != k1_relset_1(sK2,sK1,sK3) | r2_hidden(sK4,sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    spl11_1 | ~spl11_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f41,f68,f65])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X4] : (sK2 != k1_relset_1(sK2,sK1,sK3) | ~r2_hidden(k4_tarski(sK4,X4),sK3)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (27759)------------------------------
% 0.20/0.49  % (27759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (27759)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (27759)Memory used [KB]: 10874
% 0.20/0.49  % (27759)Time elapsed: 0.075 s
% 0.20/0.49  % (27759)------------------------------
% 0.20/0.49  % (27759)------------------------------
% 0.20/0.50  % (27758)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  % (27742)Success in time 0.142 s
%------------------------------------------------------------------------------
