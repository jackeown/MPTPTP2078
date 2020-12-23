%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:56 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 216 expanded)
%              Number of leaves         :   25 (  80 expanded)
%              Depth                    :   14
%              Number of atoms          :  381 (1002 expanded)
%              Number of equality atoms :   93 ( 195 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1917,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f88,f93,f98,f103,f119,f124,f196,f519,f1627,f1693,f1766,f1905])).

fof(f1905,plain,
    ( spl6_4
    | ~ spl6_82 ),
    inference(avatar_contradiction_clause,[],[f1904])).

fof(f1904,plain,
    ( $false
    | spl6_4
    | ~ spl6_82 ),
    inference(subsumption_resolution,[],[f1864,f49])).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1864,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_4
    | ~ spl6_82 ),
    inference(backward_demodulation,[],[f97,f1690])).

fof(f1690,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_82 ),
    inference(avatar_component_clause,[],[f1688])).

fof(f1688,plain,
    ( spl6_82
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).

fof(f97,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl6_4
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f1766,plain,
    ( spl6_5
    | ~ spl6_81 ),
    inference(avatar_contradiction_clause,[],[f1765])).

fof(f1765,plain,
    ( $false
    | spl6_5
    | ~ spl6_81 ),
    inference(subsumption_resolution,[],[f1696,f49])).

fof(f1696,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_5
    | ~ spl6_81 ),
    inference(backward_demodulation,[],[f102,f1686])).

fof(f1686,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_81 ),
    inference(avatar_component_clause,[],[f1684])).

fof(f1684,plain,
    ( spl6_81
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).

fof(f102,plain,
    ( ~ v1_xboole_0(sK0)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl6_5
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f1693,plain,
    ( spl6_82
    | spl6_81
    | spl6_1
    | ~ spl6_32
    | ~ spl6_79 ),
    inference(avatar_split_clause,[],[f1692,f1622,f516,f80,f1684,f1688])).

fof(f80,plain,
    ( spl6_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f516,plain,
    ( spl6_32
  <=> sK1 = k2_tarski(sK2(sK1),sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f1622,plain,
    ( spl6_79
  <=> sK1 = k2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).

fof(f1692,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | spl6_1
    | ~ spl6_32
    | ~ spl6_79 ),
    inference(subsumption_resolution,[],[f1680,f82])).

fof(f82,plain,
    ( sK0 != sK1
    | spl6_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f1680,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | sK0 = sK1
    | ~ spl6_32
    | ~ spl6_79 ),
    inference(trivial_inequality_removal,[],[f1679])).

fof(f1679,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | sK0 = sK1
    | ~ spl6_32
    | ~ spl6_79 ),
    inference(superposition,[],[f521,f1624])).

fof(f1624,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | ~ spl6_79 ),
    inference(avatar_component_clause,[],[f1622])).

fof(f521,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X0,X1) != sK1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | X0 = X1 )
    | ~ spl6_32 ),
    inference(superposition,[],[f73,f518])).

fof(f518,plain,
    ( sK1 = k2_tarski(sK2(sK1),sK2(sK1))
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f516])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k2_tarski(X0,X0) != k2_xboole_0(X1,X2) ) ),
    inference(definition_unfolding,[],[f71,f51])).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f1627,plain,
    ( spl6_79
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f1626,f85,f1622])).

fof(f85,plain,
    ( spl6_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1626,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f1618,f615])).

fof(f615,plain,
    ( ! [X2] :
        ( r2_hidden(sK5(X2,sK0,X2),sK1)
        | k2_xboole_0(X2,sK0) = X2 )
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f609,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & ~ r2_hidden(sK5(X0,X1,X2),X0) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( r2_hidden(sK5(X0,X1,X2),X1)
            | r2_hidden(sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & ~ r2_hidden(sK5(X0,X1,X2),X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( r2_hidden(sK5(X0,X1,X2),X1)
          | r2_hidden(sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f609,plain,
    ( ! [X2] :
        ( r2_hidden(sK5(X2,sK0,X2),sK1)
        | r2_hidden(sK5(X2,sK0,X2),X2)
        | k2_xboole_0(X2,sK0) = X2 )
    | ~ spl6_2 ),
    inference(factoring,[],[f259])).

fof(f259,plain,
    ( ! [X10,X9] :
        ( r2_hidden(sK5(X9,sK0,X10),sK1)
        | r2_hidden(sK5(X9,sK0,X10),X9)
        | r2_hidden(sK5(X9,sK0,X10),X10)
        | k2_xboole_0(X9,sK0) = X10 )
    | ~ spl6_2 ),
    inference(resolution,[],[f145,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f145,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(X0,sK1) )
    | ~ spl6_2 ),
    inference(resolution,[],[f87,f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f87,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f1618,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | ~ r2_hidden(sK5(sK1,sK0,sK1),sK1)
    | ~ spl6_2 ),
    inference(duplicate_literal_removal,[],[f1615])).

fof(f1615,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | sK1 = k2_xboole_0(sK1,sK0)
    | ~ r2_hidden(sK5(sK1,sK0,sK1),sK1)
    | ~ spl6_2 ),
    inference(resolution,[],[f615,f69])).

fof(f519,plain,
    ( spl6_32
    | ~ spl6_6
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f514,f191,f107,f516])).

fof(f107,plain,
    ( spl6_6
  <=> sK1 = k6_domain_1(sK1,sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f191,plain,
    ( spl6_15
  <=> k6_domain_1(sK1,sK2(sK1)) = k2_tarski(sK2(sK1),sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f514,plain,
    ( sK1 = k2_tarski(sK2(sK1),sK2(sK1))
    | ~ spl6_6
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f193,f109])).

fof(f109,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f193,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k2_tarski(sK2(sK1),sK2(sK1))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f191])).

fof(f196,plain,
    ( spl6_15
    | spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f195,f121,f95,f191])).

fof(f121,plain,
    ( spl6_7
  <=> m1_subset_1(sK2(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f195,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k2_tarski(sK2(sK1),sK2(sK1))
    | spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f188,f97])).

fof(f188,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k2_tarski(sK2(sK1),sK2(sK1))
    | v1_xboole_0(sK1)
    | ~ spl6_7 ),
    inference(resolution,[],[f123,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f57,f51])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f123,plain,
    ( m1_subset_1(sK2(sK1),sK1)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f124,plain,
    ( spl6_7
    | ~ spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f112,f95,f90,f121])).

fof(f90,plain,
    ( spl6_3
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f112,plain,
    ( m1_subset_1(sK2(sK1),sK1)
    | ~ spl6_3
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f92,f97,f52])).

fof(f52,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK2(X0)) = X0
            & m1_subset_1(sK2(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK2(X0)) = X0
        & m1_subset_1(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f92,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f119,plain,
    ( spl6_6
    | ~ spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f113,f95,f90,f107])).

fof(f113,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | ~ spl6_3
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f92,f97,f53])).

fof(f53,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK2(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f103,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f44,f100])).

fof(f44,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK0 != sK1
    & r1_tarski(sK0,sK1)
    & v1_zfmisc_1(sK1)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r1_tarski(X0,X1)
            & v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & r1_tarski(sK0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( sK0 != X1
        & r1_tarski(sK0,X1)
        & v1_zfmisc_1(X1)
        & ~ v1_xboole_0(X1) )
   => ( sK0 != sK1
      & r1_tarski(sK0,sK1)
      & v1_zfmisc_1(sK1)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f98,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f45,f95])).

fof(f45,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f93,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f46,f90])).

fof(f46,plain,(
    v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f88,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f47,f85])).

fof(f47,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f83,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f48,f80])).

fof(f48,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:26:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (32679)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  % (32694)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.50  % (32686)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.50  % (32679)Refutation not found, incomplete strategy% (32679)------------------------------
% 0.20/0.50  % (32679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (32679)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (32679)Memory used [KB]: 10746
% 0.20/0.50  % (32679)Time elapsed: 0.095 s
% 0.20/0.50  % (32679)------------------------------
% 0.20/0.50  % (32679)------------------------------
% 0.20/0.51  % (32695)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (32694)Refutation not found, incomplete strategy% (32694)------------------------------
% 0.20/0.51  % (32694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (32681)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (32694)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (32694)Memory used [KB]: 10618
% 0.20/0.51  % (32694)Time elapsed: 0.109 s
% 0.20/0.51  % (32694)------------------------------
% 0.20/0.51  % (32694)------------------------------
% 0.20/0.51  % (32682)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (32699)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (32680)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (32705)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (32703)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.52  % (32687)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (32697)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (32691)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (32689)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (32684)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (32685)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (32683)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (32690)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (32685)Refutation not found, incomplete strategy% (32685)------------------------------
% 0.20/0.53  % (32685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (32685)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (32685)Memory used [KB]: 10746
% 0.20/0.53  % (32685)Time elapsed: 0.127 s
% 0.20/0.53  % (32685)------------------------------
% 0.20/0.53  % (32685)------------------------------
% 0.20/0.54  % (32699)Refutation not found, incomplete strategy% (32699)------------------------------
% 0.20/0.54  % (32699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (32699)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (32699)Memory used [KB]: 10746
% 0.20/0.54  % (32699)Time elapsed: 0.090 s
% 0.20/0.54  % (32699)------------------------------
% 0.20/0.54  % (32699)------------------------------
% 0.20/0.54  % (32678)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (32677)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (32696)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (32702)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (32706)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (32700)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.49/0.55  % (32698)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.49/0.55  % (32688)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.49/0.55  % (32701)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.49/0.55  % (32692)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.49/0.56  % (32704)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.49/0.56  % (32693)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.60/0.60  % (32702)Refutation found. Thanks to Tanya!
% 1.60/0.60  % SZS status Theorem for theBenchmark
% 1.60/0.62  % (32708)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.60/0.63  % (32707)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.60/0.63  % SZS output start Proof for theBenchmark
% 1.60/0.63  fof(f1917,plain,(
% 1.60/0.63    $false),
% 1.60/0.63    inference(avatar_sat_refutation,[],[f83,f88,f93,f98,f103,f119,f124,f196,f519,f1627,f1693,f1766,f1905])).
% 1.60/0.63  fof(f1905,plain,(
% 1.60/0.63    spl6_4 | ~spl6_82),
% 1.60/0.63    inference(avatar_contradiction_clause,[],[f1904])).
% 1.60/0.63  fof(f1904,plain,(
% 1.60/0.63    $false | (spl6_4 | ~spl6_82)),
% 1.60/0.63    inference(subsumption_resolution,[],[f1864,f49])).
% 1.60/0.63  fof(f49,plain,(
% 1.60/0.63    v1_xboole_0(k1_xboole_0)),
% 1.60/0.63    inference(cnf_transformation,[],[f4])).
% 1.60/0.63  fof(f4,axiom,(
% 1.60/0.63    v1_xboole_0(k1_xboole_0)),
% 1.60/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.60/0.63  fof(f1864,plain,(
% 1.60/0.63    ~v1_xboole_0(k1_xboole_0) | (spl6_4 | ~spl6_82)),
% 1.60/0.63    inference(backward_demodulation,[],[f97,f1690])).
% 1.60/0.63  fof(f1690,plain,(
% 1.60/0.63    k1_xboole_0 = sK1 | ~spl6_82),
% 1.60/0.63    inference(avatar_component_clause,[],[f1688])).
% 1.60/0.63  fof(f1688,plain,(
% 1.60/0.63    spl6_82 <=> k1_xboole_0 = sK1),
% 1.60/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).
% 1.60/0.63  fof(f97,plain,(
% 1.60/0.63    ~v1_xboole_0(sK1) | spl6_4),
% 1.60/0.63    inference(avatar_component_clause,[],[f95])).
% 1.60/0.63  fof(f95,plain,(
% 1.60/0.63    spl6_4 <=> v1_xboole_0(sK1)),
% 1.60/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.60/0.63  fof(f1766,plain,(
% 1.60/0.63    spl6_5 | ~spl6_81),
% 1.60/0.63    inference(avatar_contradiction_clause,[],[f1765])).
% 1.60/0.63  fof(f1765,plain,(
% 1.60/0.63    $false | (spl6_5 | ~spl6_81)),
% 1.60/0.63    inference(subsumption_resolution,[],[f1696,f49])).
% 1.60/0.63  fof(f1696,plain,(
% 1.60/0.63    ~v1_xboole_0(k1_xboole_0) | (spl6_5 | ~spl6_81)),
% 1.60/0.63    inference(backward_demodulation,[],[f102,f1686])).
% 1.60/0.63  fof(f1686,plain,(
% 1.60/0.63    k1_xboole_0 = sK0 | ~spl6_81),
% 1.60/0.63    inference(avatar_component_clause,[],[f1684])).
% 1.60/0.63  fof(f1684,plain,(
% 1.60/0.63    spl6_81 <=> k1_xboole_0 = sK0),
% 1.60/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).
% 1.60/0.63  fof(f102,plain,(
% 1.60/0.63    ~v1_xboole_0(sK0) | spl6_5),
% 1.60/0.63    inference(avatar_component_clause,[],[f100])).
% 1.60/0.63  fof(f100,plain,(
% 1.60/0.63    spl6_5 <=> v1_xboole_0(sK0)),
% 1.60/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.60/0.63  fof(f1693,plain,(
% 1.60/0.63    spl6_82 | spl6_81 | spl6_1 | ~spl6_32 | ~spl6_79),
% 1.60/0.63    inference(avatar_split_clause,[],[f1692,f1622,f516,f80,f1684,f1688])).
% 1.60/0.63  fof(f80,plain,(
% 1.60/0.63    spl6_1 <=> sK0 = sK1),
% 1.60/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.60/0.63  fof(f516,plain,(
% 1.60/0.63    spl6_32 <=> sK1 = k2_tarski(sK2(sK1),sK2(sK1))),
% 1.60/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 1.60/0.63  fof(f1622,plain,(
% 1.60/0.63    spl6_79 <=> sK1 = k2_xboole_0(sK1,sK0)),
% 1.60/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).
% 2.06/0.63  fof(f1692,plain,(
% 2.06/0.63    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | (spl6_1 | ~spl6_32 | ~spl6_79)),
% 2.06/0.63    inference(subsumption_resolution,[],[f1680,f82])).
% 2.06/0.63  fof(f82,plain,(
% 2.06/0.63    sK0 != sK1 | spl6_1),
% 2.06/0.63    inference(avatar_component_clause,[],[f80])).
% 2.06/0.63  fof(f1680,plain,(
% 2.06/0.63    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | sK0 = sK1 | (~spl6_32 | ~spl6_79)),
% 2.06/0.63    inference(trivial_inequality_removal,[],[f1679])).
% 2.06/0.63  fof(f1679,plain,(
% 2.06/0.63    sK1 != sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | sK0 = sK1 | (~spl6_32 | ~spl6_79)),
% 2.06/0.63    inference(superposition,[],[f521,f1624])).
% 2.06/0.63  fof(f1624,plain,(
% 2.06/0.63    sK1 = k2_xboole_0(sK1,sK0) | ~spl6_79),
% 2.06/0.63    inference(avatar_component_clause,[],[f1622])).
% 2.06/0.63  fof(f521,plain,(
% 2.06/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) != sK1 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X0 = X1) ) | ~spl6_32),
% 2.06/0.63    inference(superposition,[],[f73,f518])).
% 2.06/0.63  fof(f518,plain,(
% 2.06/0.63    sK1 = k2_tarski(sK2(sK1),sK2(sK1)) | ~spl6_32),
% 2.06/0.63    inference(avatar_component_clause,[],[f516])).
% 2.06/0.63  fof(f73,plain,(
% 2.06/0.63    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k2_tarski(X0,X0) != k2_xboole_0(X1,X2)) )),
% 2.06/0.63    inference(definition_unfolding,[],[f71,f51])).
% 2.06/0.63  fof(f51,plain,(
% 2.06/0.63    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f7])).
% 2.06/0.63  fof(f7,axiom,(
% 2.06/0.63    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.06/0.63  fof(f71,plain,(
% 2.06/0.63    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k1_tarski(X0) != k2_xboole_0(X1,X2)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f21])).
% 2.06/0.63  fof(f21,plain,(
% 2.06/0.63    ! [X0,X1,X2] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k1_tarski(X0) != k2_xboole_0(X1,X2))),
% 2.06/0.63    inference(ennf_transformation,[],[f8])).
% 2.06/0.63  fof(f8,axiom,(
% 2.06/0.63    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 2.06/0.63  fof(f1627,plain,(
% 2.06/0.63    spl6_79 | ~spl6_2),
% 2.06/0.63    inference(avatar_split_clause,[],[f1626,f85,f1622])).
% 2.06/0.63  fof(f85,plain,(
% 2.06/0.63    spl6_2 <=> r1_tarski(sK0,sK1)),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.06/0.63  fof(f1626,plain,(
% 2.06/0.63    sK1 = k2_xboole_0(sK1,sK0) | ~spl6_2),
% 2.06/0.63    inference(subsumption_resolution,[],[f1618,f615])).
% 2.06/0.63  fof(f615,plain,(
% 2.06/0.63    ( ! [X2] : (r2_hidden(sK5(X2,sK0,X2),sK1) | k2_xboole_0(X2,sK0) = X2) ) | ~spl6_2),
% 2.06/0.63    inference(subsumption_resolution,[],[f609,f69])).
% 2.06/0.63  fof(f69,plain,(
% 2.06/0.63    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f43])).
% 2.06/0.63  fof(f43,plain,(
% 2.06/0.63    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.06/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).
% 2.06/0.63  fof(f42,plain,(
% 2.06/0.63    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 2.06/0.63    introduced(choice_axiom,[])).
% 2.06/0.63  fof(f41,plain,(
% 2.06/0.63    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.06/0.63    inference(rectify,[],[f40])).
% 2.06/0.63  fof(f40,plain,(
% 2.06/0.63    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.06/0.63    inference(flattening,[],[f39])).
% 2.06/0.63  fof(f39,plain,(
% 2.06/0.63    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.06/0.63    inference(nnf_transformation,[],[f3])).
% 2.06/0.63  fof(f3,axiom,(
% 2.06/0.63    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 2.06/0.63  fof(f609,plain,(
% 2.06/0.63    ( ! [X2] : (r2_hidden(sK5(X2,sK0,X2),sK1) | r2_hidden(sK5(X2,sK0,X2),X2) | k2_xboole_0(X2,sK0) = X2) ) | ~spl6_2),
% 2.06/0.63    inference(factoring,[],[f259])).
% 2.06/0.63  fof(f259,plain,(
% 2.06/0.63    ( ! [X10,X9] : (r2_hidden(sK5(X9,sK0,X10),sK1) | r2_hidden(sK5(X9,sK0,X10),X9) | r2_hidden(sK5(X9,sK0,X10),X10) | k2_xboole_0(X9,sK0) = X10) ) | ~spl6_2),
% 2.06/0.63    inference(resolution,[],[f145,f68])).
% 2.06/0.63  fof(f68,plain,(
% 2.06/0.63    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f43])).
% 2.06/0.63  fof(f145,plain,(
% 2.06/0.63    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(X0,sK1)) ) | ~spl6_2),
% 2.06/0.63    inference(resolution,[],[f87,f61])).
% 2.06/0.63  fof(f61,plain,(
% 2.06/0.63    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f38])).
% 2.06/0.63  fof(f38,plain,(
% 2.06/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.06/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 2.06/0.63  fof(f37,plain,(
% 2.06/0.63    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.06/0.63    introduced(choice_axiom,[])).
% 2.06/0.63  fof(f36,plain,(
% 2.06/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.06/0.63    inference(rectify,[],[f35])).
% 2.06/0.63  fof(f35,plain,(
% 2.06/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.06/0.63    inference(nnf_transformation,[],[f19])).
% 2.06/0.63  fof(f19,plain,(
% 2.06/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.06/0.63    inference(ennf_transformation,[],[f2])).
% 2.06/0.63  fof(f2,axiom,(
% 2.06/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.06/0.63  fof(f87,plain,(
% 2.06/0.63    r1_tarski(sK0,sK1) | ~spl6_2),
% 2.06/0.63    inference(avatar_component_clause,[],[f85])).
% 2.06/0.63  fof(f1618,plain,(
% 2.06/0.63    sK1 = k2_xboole_0(sK1,sK0) | ~r2_hidden(sK5(sK1,sK0,sK1),sK1) | ~spl6_2),
% 2.06/0.63    inference(duplicate_literal_removal,[],[f1615])).
% 2.06/0.63  fof(f1615,plain,(
% 2.06/0.63    sK1 = k2_xboole_0(sK1,sK0) | sK1 = k2_xboole_0(sK1,sK0) | ~r2_hidden(sK5(sK1,sK0,sK1),sK1) | ~spl6_2),
% 2.06/0.63    inference(resolution,[],[f615,f69])).
% 2.06/0.63  fof(f519,plain,(
% 2.06/0.63    spl6_32 | ~spl6_6 | ~spl6_15),
% 2.06/0.63    inference(avatar_split_clause,[],[f514,f191,f107,f516])).
% 2.06/0.63  fof(f107,plain,(
% 2.06/0.63    spl6_6 <=> sK1 = k6_domain_1(sK1,sK2(sK1))),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.06/0.63  fof(f191,plain,(
% 2.06/0.63    spl6_15 <=> k6_domain_1(sK1,sK2(sK1)) = k2_tarski(sK2(sK1),sK2(sK1))),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 2.06/0.63  fof(f514,plain,(
% 2.06/0.63    sK1 = k2_tarski(sK2(sK1),sK2(sK1)) | (~spl6_6 | ~spl6_15)),
% 2.06/0.63    inference(forward_demodulation,[],[f193,f109])).
% 2.06/0.63  fof(f109,plain,(
% 2.06/0.63    sK1 = k6_domain_1(sK1,sK2(sK1)) | ~spl6_6),
% 2.06/0.63    inference(avatar_component_clause,[],[f107])).
% 2.06/0.63  fof(f193,plain,(
% 2.06/0.63    k6_domain_1(sK1,sK2(sK1)) = k2_tarski(sK2(sK1),sK2(sK1)) | ~spl6_15),
% 2.06/0.63    inference(avatar_component_clause,[],[f191])).
% 2.06/0.63  fof(f196,plain,(
% 2.06/0.63    spl6_15 | spl6_4 | ~spl6_7),
% 2.06/0.63    inference(avatar_split_clause,[],[f195,f121,f95,f191])).
% 2.06/0.63  fof(f121,plain,(
% 2.06/0.63    spl6_7 <=> m1_subset_1(sK2(sK1),sK1)),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.06/0.63  fof(f195,plain,(
% 2.06/0.63    k6_domain_1(sK1,sK2(sK1)) = k2_tarski(sK2(sK1),sK2(sK1)) | (spl6_4 | ~spl6_7)),
% 2.06/0.63    inference(subsumption_resolution,[],[f188,f97])).
% 2.06/0.63  fof(f188,plain,(
% 2.06/0.63    k6_domain_1(sK1,sK2(sK1)) = k2_tarski(sK2(sK1),sK2(sK1)) | v1_xboole_0(sK1) | ~spl6_7),
% 2.06/0.63    inference(resolution,[],[f123,f72])).
% 2.06/0.63  fof(f72,plain,(
% 2.06/0.63    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k2_tarski(X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.06/0.63    inference(definition_unfolding,[],[f57,f51])).
% 2.06/0.63  fof(f57,plain,(
% 2.06/0.63    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f18])).
% 2.06/0.63  fof(f18,plain,(
% 2.06/0.63    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.06/0.63    inference(flattening,[],[f17])).
% 2.06/0.63  fof(f17,plain,(
% 2.06/0.63    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.06/0.63    inference(ennf_transformation,[],[f10])).
% 2.06/0.63  fof(f10,axiom,(
% 2.06/0.63    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 2.06/0.63  fof(f123,plain,(
% 2.06/0.63    m1_subset_1(sK2(sK1),sK1) | ~spl6_7),
% 2.06/0.63    inference(avatar_component_clause,[],[f121])).
% 2.06/0.63  fof(f124,plain,(
% 2.06/0.63    spl6_7 | ~spl6_3 | spl6_4),
% 2.06/0.63    inference(avatar_split_clause,[],[f112,f95,f90,f121])).
% 2.06/0.63  fof(f90,plain,(
% 2.06/0.63    spl6_3 <=> v1_zfmisc_1(sK1)),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.06/0.63  fof(f112,plain,(
% 2.06/0.63    m1_subset_1(sK2(sK1),sK1) | (~spl6_3 | spl6_4)),
% 2.06/0.63    inference(unit_resulting_resolution,[],[f92,f97,f52])).
% 2.06/0.63  fof(f52,plain,(
% 2.06/0.63    ( ! [X0] : (m1_subset_1(sK2(X0),X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f28])).
% 2.06/0.63  fof(f28,plain,(
% 2.06/0.63    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.06/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).
% 2.06/0.63  fof(f27,plain,(
% 2.06/0.63    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)))),
% 2.06/0.63    introduced(choice_axiom,[])).
% 2.06/0.63  fof(f26,plain,(
% 2.06/0.63    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.06/0.63    inference(rectify,[],[f25])).
% 2.06/0.63  fof(f25,plain,(
% 2.06/0.63    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.06/0.63    inference(nnf_transformation,[],[f16])).
% 2.06/0.63  fof(f16,plain,(
% 2.06/0.63    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 2.06/0.63    inference(ennf_transformation,[],[f11])).
% 2.06/0.63  fof(f11,axiom,(
% 2.06/0.63    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
% 2.06/0.63  fof(f92,plain,(
% 2.06/0.63    v1_zfmisc_1(sK1) | ~spl6_3),
% 2.06/0.63    inference(avatar_component_clause,[],[f90])).
% 2.06/0.63  fof(f119,plain,(
% 2.06/0.63    spl6_6 | ~spl6_3 | spl6_4),
% 2.06/0.63    inference(avatar_split_clause,[],[f113,f95,f90,f107])).
% 2.06/0.63  fof(f113,plain,(
% 2.06/0.63    sK1 = k6_domain_1(sK1,sK2(sK1)) | (~spl6_3 | spl6_4)),
% 2.06/0.63    inference(unit_resulting_resolution,[],[f92,f97,f53])).
% 2.06/0.63  fof(f53,plain,(
% 2.06/0.63    ( ! [X0] : (k6_domain_1(X0,sK2(X0)) = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f28])).
% 2.06/0.63  fof(f103,plain,(
% 2.06/0.63    ~spl6_5),
% 2.06/0.63    inference(avatar_split_clause,[],[f44,f100])).
% 2.06/0.63  fof(f44,plain,(
% 2.06/0.63    ~v1_xboole_0(sK0)),
% 2.06/0.63    inference(cnf_transformation,[],[f24])).
% 2.06/0.63  fof(f24,plain,(
% 2.06/0.63    (sK0 != sK1 & r1_tarski(sK0,sK1) & v1_zfmisc_1(sK1) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 2.06/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f23,f22])).
% 2.06/0.63  fof(f22,plain,(
% 2.06/0.63    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (sK0 != X1 & r1_tarski(sK0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 2.06/0.63    introduced(choice_axiom,[])).
% 2.06/0.63  fof(f23,plain,(
% 2.06/0.63    ? [X1] : (sK0 != X1 & r1_tarski(sK0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (sK0 != sK1 & r1_tarski(sK0,sK1) & v1_zfmisc_1(sK1) & ~v1_xboole_0(sK1))),
% 2.06/0.63    introduced(choice_axiom,[])).
% 2.06/0.63  fof(f15,plain,(
% 2.06/0.63    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.06/0.63    inference(flattening,[],[f14])).
% 2.06/0.63  fof(f14,plain,(
% 2.06/0.63    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 2.06/0.63    inference(ennf_transformation,[],[f13])).
% 2.06/0.63  fof(f13,negated_conjecture,(
% 2.06/0.63    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.06/0.63    inference(negated_conjecture,[],[f12])).
% 2.06/0.63  fof(f12,conjecture,(
% 2.06/0.63    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 2.06/0.63  fof(f98,plain,(
% 2.06/0.63    ~spl6_4),
% 2.06/0.63    inference(avatar_split_clause,[],[f45,f95])).
% 2.06/0.63  fof(f45,plain,(
% 2.06/0.63    ~v1_xboole_0(sK1)),
% 2.06/0.63    inference(cnf_transformation,[],[f24])).
% 2.06/0.63  fof(f93,plain,(
% 2.06/0.63    spl6_3),
% 2.06/0.63    inference(avatar_split_clause,[],[f46,f90])).
% 2.06/0.63  fof(f46,plain,(
% 2.06/0.63    v1_zfmisc_1(sK1)),
% 2.06/0.63    inference(cnf_transformation,[],[f24])).
% 2.06/0.63  fof(f88,plain,(
% 2.06/0.63    spl6_2),
% 2.06/0.63    inference(avatar_split_clause,[],[f47,f85])).
% 2.06/0.63  fof(f47,plain,(
% 2.06/0.63    r1_tarski(sK0,sK1)),
% 2.06/0.63    inference(cnf_transformation,[],[f24])).
% 2.06/0.63  fof(f83,plain,(
% 2.06/0.63    ~spl6_1),
% 2.06/0.63    inference(avatar_split_clause,[],[f48,f80])).
% 2.06/0.63  fof(f48,plain,(
% 2.06/0.63    sK0 != sK1),
% 2.06/0.63    inference(cnf_transformation,[],[f24])).
% 2.06/0.63  % SZS output end Proof for theBenchmark
% 2.06/0.63  % (32702)------------------------------
% 2.06/0.63  % (32702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.63  % (32702)Termination reason: Refutation
% 2.06/0.63  
% 2.06/0.63  % (32702)Memory used [KB]: 7164
% 2.06/0.63  % (32702)Time elapsed: 0.210 s
% 2.06/0.63  % (32702)------------------------------
% 2.06/0.63  % (32702)------------------------------
% 2.06/0.63  % (32676)Success in time 0.269 s
%------------------------------------------------------------------------------
