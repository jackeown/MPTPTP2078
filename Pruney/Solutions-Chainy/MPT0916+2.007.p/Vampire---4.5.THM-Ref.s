%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:38 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 318 expanded)
%              Number of leaves         :   48 ( 153 expanded)
%              Depth                    :    8
%              Number of atoms          :  460 (1182 expanded)
%              Number of equality atoms :   73 ( 134 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f346,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f61,f66,f72,f79,f86,f92,f97,f106,f115,f123,f129,f134,f152,f157,f163,f176,f182,f191,f205,f209,f213,f231,f235,f249,f259,f260,f307,f316,f317,f340,f344,f345])).

fof(f345,plain,
    ( k1_xboole_0 != sK1
    | sK1 != sK4
    | v1_xboole_0(sK4)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f344,plain,(
    spl7_42 ),
    inference(avatar_contradiction_clause,[],[f341])).

fof(f341,plain,
    ( $false
    | spl7_42 ),
    inference(unit_resulting_resolution,[],[f32,f339])).

fof(f339,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4)
    | spl7_42 ),
    inference(avatar_component_clause,[],[f337])).

fof(f337,plain,
    ( spl7_42
  <=> r1_tarski(k1_xboole_0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f340,plain,
    ( ~ spl7_42
    | spl7_11
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f321,f198,f108,f337])).

fof(f108,plain,
    ( spl7_11
  <=> r1_tarski(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f198,plain,
    ( spl7_28
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f321,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4)
    | spl7_11
    | ~ spl7_28 ),
    inference(backward_demodulation,[],[f110,f200])).

fof(f200,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f198])).

fof(f110,plain,
    ( ~ r1_tarski(sK1,sK4)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f108])).

fof(f317,plain,
    ( k1_xboole_0 != sK2
    | sK2 != sK5
    | v1_xboole_0(sK5)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f316,plain,(
    spl7_38 ),
    inference(avatar_contradiction_clause,[],[f313])).

fof(f313,plain,
    ( $false
    | spl7_38 ),
    inference(unit_resulting_resolution,[],[f32,f306])).

fof(f306,plain,
    ( ~ r1_tarski(k1_xboole_0,sK5)
    | spl7_38 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl7_38
  <=> r1_tarski(k1_xboole_0,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f307,plain,
    ( ~ spl7_38
    | spl7_25
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f264,f202,f184,f304])).

fof(f184,plain,
    ( spl7_25
  <=> r1_tarski(sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f202,plain,
    ( spl7_29
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f264,plain,
    ( ~ r1_tarski(k1_xboole_0,sK5)
    | spl7_25
    | ~ spl7_29 ),
    inference(backward_demodulation,[],[f186,f204])).

fof(f204,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f202])).

fof(f186,plain,
    ( ~ r1_tarski(sK2,sK5)
    | spl7_25 ),
    inference(avatar_component_clause,[],[f184])).

fof(f260,plain,
    ( k1_xboole_0 != sK3
    | v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f259,plain,(
    spl7_33 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | spl7_33 ),
    inference(unit_resulting_resolution,[],[f31,f254])).

fof(f254,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl7_33 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl7_33
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f31,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f249,plain,
    ( spl7_32
    | ~ spl7_10
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f236,f194,f103,f246])).

fof(f246,plain,
    ( spl7_32
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f103,plain,
    ( spl7_10
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f194,plain,
    ( spl7_27
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f236,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_10
    | ~ spl7_27 ),
    inference(forward_demodulation,[],[f105,f196])).

fof(f196,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f194])).

fof(f105,plain,
    ( sK0 = sK3
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f103])).

fof(f235,plain,(
    spl7_31 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | spl7_31 ),
    inference(unit_resulting_resolution,[],[f32,f230])).

fof(f230,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | spl7_31 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl7_31
  <=> r1_tarski(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f231,plain,
    ( ~ spl7_31
    | spl7_9
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f218,f194,f99,f228])).

fof(f99,plain,
    ( spl7_9
  <=> r1_tarski(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f218,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | spl7_9
    | ~ spl7_27 ),
    inference(backward_demodulation,[],[f101,f196])).

fof(f101,plain,
    ( ~ r1_tarski(sK0,sK3)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f213,plain,
    ( spl7_27
    | spl7_28
    | spl7_29
    | ~ spl7_8
    | ~ spl7_19
    | spl7_22 ),
    inference(avatar_split_clause,[],[f210,f169,f154,f94,f202,f198,f194])).

fof(f94,plain,
    ( spl7_8
  <=> m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f154,plain,
    ( spl7_19
  <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f169,plain,
    ( spl7_22
  <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f210,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl7_22 ),
    inference(superposition,[],[f171,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f43,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f171,plain,
    ( ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | spl7_22 ),
    inference(avatar_component_clause,[],[f169])).

fof(f209,plain,
    ( spl7_27
    | spl7_28
    | spl7_29
    | ~ spl7_8
    | ~ spl7_13
    | spl7_23 ),
    inference(avatar_split_clause,[],[f208,f173,f120,f94,f202,f198,f194])).

fof(f120,plain,
    ( spl7_13
  <=> r2_hidden(k2_mcart_1(sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f173,plain,
    ( spl7_23
  <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f208,plain,
    ( ~ r2_hidden(k2_mcart_1(sK6),sK5)
    | ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl7_23 ),
    inference(superposition,[],[f175,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f44,f39])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f175,plain,
    ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | spl7_23 ),
    inference(avatar_component_clause,[],[f173])).

fof(f205,plain,
    ( spl7_27
    | spl7_28
    | spl7_29
    | ~ spl7_8
    | ~ spl7_18
    | spl7_21 ),
    inference(avatar_split_clause,[],[f192,f165,f149,f94,f202,f198,f194])).

fof(f149,plain,
    ( spl7_18
  <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f165,plain,
    ( spl7_21
  <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f192,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl7_21 ),
    inference(superposition,[],[f167,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f42,f39])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f167,plain,
    ( ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | spl7_21 ),
    inference(avatar_component_clause,[],[f165])).

fof(f191,plain,
    ( ~ spl7_25
    | spl7_26
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f87,f83,f188,f184])).

fof(f188,plain,
    ( spl7_26
  <=> sK2 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f83,plain,
    ( spl7_6
  <=> r1_tarski(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f87,plain,
    ( sK2 = sK5
    | ~ r1_tarski(sK2,sK5)
    | ~ spl7_6 ),
    inference(resolution,[],[f85,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f85,plain,
    ( r1_tarski(sK5,sK2)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f182,plain,
    ( ~ spl7_24
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f177,f154,f179])).

fof(f179,plain,
    ( spl7_24
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f177,plain,
    ( ~ v1_xboole_0(sK4)
    | ~ spl7_19 ),
    inference(resolution,[],[f156,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f156,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f154])).

fof(f176,plain,
    ( ~ spl7_21
    | ~ spl7_22
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f30,f173,f169,f165])).

fof(f30,plain,
    ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
      | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
      | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) )
    & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f13,f20,f19,f18,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                    & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                    & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
                & m1_subset_1(X5,k1_zfmisc_1(X2)) )
            & m1_subset_1(X4,k1_zfmisc_1(X1)) )
        & m1_subset_1(X3,k1_zfmisc_1(X0)) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
                  & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
              & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
          & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
                  | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4)
                  | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
                & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5))
                & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
            & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
        & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
                | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
                | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
              & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5))
              & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
          & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
              | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
              | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
            & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5))
            & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
        & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
   => ( ? [X6] :
          ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5)
            | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
            | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
          & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5))
          & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
      & m1_subset_1(sK5,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X6] :
        ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5)
          | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
          | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
        & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5))
        & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
   => ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
        | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
        | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) )
      & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))
      & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X0))
       => ! [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(X1))
           => ! [X5] :
                ( m1_subset_1(X5,k1_zfmisc_1(X2))
               => ! [X6] :
                    ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                   => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                     => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                        & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                        & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X0))
     => ! [X4] :
          ( m1_subset_1(X4,k1_zfmisc_1(X1))
         => ! [X5] :
              ( m1_subset_1(X5,k1_zfmisc_1(X2))
             => ! [X6] :
                  ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                 => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                   => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).

fof(f163,plain,
    ( ~ spl7_20
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f158,f149,f160])).

fof(f160,plain,
    ( spl7_20
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f158,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl7_18 ),
    inference(resolution,[],[f151,f33])).

fof(f151,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f149])).

fof(f157,plain,
    ( spl7_19
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f141,f131,f154])).

fof(f131,plain,
    ( spl7_15
  <=> r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f141,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | ~ spl7_15 ),
    inference(resolution,[],[f133,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f133,plain,
    ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f131])).

fof(f152,plain,
    ( spl7_18
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f140,f131,f149])).

fof(f140,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ spl7_15 ),
    inference(resolution,[],[f133,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f134,plain,
    ( spl7_15
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f116,f89,f131])).

fof(f89,plain,
    ( spl7_7
  <=> r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f116,plain,
    ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))
    | ~ spl7_7 ),
    inference(resolution,[],[f91,f40])).

fof(f91,plain,
    ( r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f89])).

fof(f129,plain,
    ( ~ spl7_14
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f124,f120,f126])).

fof(f126,plain,
    ( spl7_14
  <=> v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f124,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ spl7_13 ),
    inference(resolution,[],[f122,f33])).

fof(f122,plain,
    ( r2_hidden(k2_mcart_1(sK6),sK5)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f120])).

fof(f123,plain,
    ( spl7_13
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f117,f89,f120])).

fof(f117,plain,
    ( r2_hidden(k2_mcart_1(sK6),sK5)
    | ~ spl7_7 ),
    inference(resolution,[],[f91,f41])).

fof(f115,plain,
    ( ~ spl7_11
    | spl7_12
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f80,f76,f112,f108])).

fof(f112,plain,
    ( spl7_12
  <=> sK1 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f76,plain,
    ( spl7_5
  <=> r1_tarski(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f80,plain,
    ( sK1 = sK4
    | ~ r1_tarski(sK1,sK4)
    | ~ spl7_5 ),
    inference(resolution,[],[f78,f36])).

fof(f78,plain,
    ( r1_tarski(sK4,sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f106,plain,
    ( ~ spl7_9
    | spl7_10
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f73,f69,f103,f99])).

fof(f69,plain,
    ( spl7_4
  <=> r1_tarski(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f73,plain,
    ( sK0 = sK3
    | ~ r1_tarski(sK0,sK3)
    | ~ spl7_4 ),
    inference(resolution,[],[f71,f36])).

fof(f71,plain,
    ( r1_tarski(sK3,sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f97,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f46,f94])).

fof(f46,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f28,f39])).

fof(f28,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f92,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f45,f89])).

fof(f45,plain,(
    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f29,f39])).

fof(f29,plain,(
    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f21])).

fof(f86,plain,
    ( spl7_6
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f81,f63,f83])).

fof(f63,plain,
    ( spl7_3
  <=> m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f81,plain,
    ( r1_tarski(sK5,sK2)
    | ~ spl7_3 ),
    inference(resolution,[],[f65,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f65,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f79,plain,
    ( spl7_5
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f74,f58,f76])).

fof(f58,plain,
    ( spl7_2
  <=> m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f74,plain,
    ( r1_tarski(sK4,sK1)
    | ~ spl7_2 ),
    inference(resolution,[],[f60,f37])).

fof(f60,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f72,plain,
    ( spl7_4
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f67,f53,f69])).

fof(f53,plain,
    ( spl7_1
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f67,plain,
    ( r1_tarski(sK3,sK0)
    | ~ spl7_1 ),
    inference(resolution,[],[f55,f37])).

fof(f55,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f66,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f26,f58])).

fof(f26,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f25,f53])).

fof(f25,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 1.34/0.54  % (26122)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.34/0.54  % (26113)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.49/0.55  % (26108)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.49/0.56  % (26122)Refutation not found, incomplete strategy% (26122)------------------------------
% 1.49/0.56  % (26122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (26130)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.49/0.56  % (26116)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.49/0.57  % (26111)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.49/0.57  % (26126)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.49/0.57  % (26124)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.49/0.57  % (26131)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.49/0.57  % (26128)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.49/0.57  % (26109)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.49/0.57  % (26120)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.49/0.57  % (26131)Refutation not found, incomplete strategy% (26131)------------------------------
% 1.49/0.57  % (26131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (26131)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.57  
% 1.49/0.57  % (26131)Memory used [KB]: 10746
% 1.49/0.57  % (26131)Time elapsed: 0.162 s
% 1.49/0.57  % (26131)------------------------------
% 1.49/0.57  % (26131)------------------------------
% 1.49/0.57  % (26122)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.57  
% 1.49/0.57  % (26122)Memory used [KB]: 10618
% 1.49/0.57  % (26122)Time elapsed: 0.157 s
% 1.49/0.57  % (26122)------------------------------
% 1.49/0.57  % (26122)------------------------------
% 1.49/0.58  % (26120)Refutation not found, incomplete strategy% (26120)------------------------------
% 1.49/0.58  % (26120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.58  % (26135)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.49/0.58  % (26116)Refutation found. Thanks to Tanya!
% 1.49/0.58  % SZS status Theorem for theBenchmark
% 1.49/0.58  % (26112)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.49/0.58  % (26120)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.58  
% 1.49/0.58  % (26120)Memory used [KB]: 1791
% 1.49/0.58  % (26120)Time elapsed: 0.088 s
% 1.49/0.58  % (26120)------------------------------
% 1.49/0.58  % (26120)------------------------------
% 1.49/0.58  % (26118)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.49/0.58  % (26136)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.49/0.59  % (26136)Refutation not found, incomplete strategy% (26136)------------------------------
% 1.49/0.59  % (26136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.59  % (26136)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.59  
% 1.49/0.59  % (26136)Memory used [KB]: 1663
% 1.49/0.59  % (26136)Time elapsed: 0.157 s
% 1.49/0.59  % (26136)------------------------------
% 1.49/0.59  % (26136)------------------------------
% 1.49/0.59  % (26119)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.49/0.59  % (26133)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.49/0.59  % (26124)Refutation not found, incomplete strategy% (26124)------------------------------
% 1.49/0.59  % (26124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.59  % SZS output start Proof for theBenchmark
% 1.49/0.59  fof(f346,plain,(
% 1.49/0.59    $false),
% 1.49/0.59    inference(avatar_sat_refutation,[],[f56,f61,f66,f72,f79,f86,f92,f97,f106,f115,f123,f129,f134,f152,f157,f163,f176,f182,f191,f205,f209,f213,f231,f235,f249,f259,f260,f307,f316,f317,f340,f344,f345])).
% 1.49/0.59  fof(f345,plain,(
% 1.49/0.59    k1_xboole_0 != sK1 | sK1 != sK4 | v1_xboole_0(sK4) | ~v1_xboole_0(k1_xboole_0)),
% 1.49/0.59    introduced(theory_tautology_sat_conflict,[])).
% 1.49/0.59  fof(f344,plain,(
% 1.49/0.59    spl7_42),
% 1.49/0.59    inference(avatar_contradiction_clause,[],[f341])).
% 1.49/0.59  fof(f341,plain,(
% 1.49/0.59    $false | spl7_42),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f32,f339])).
% 1.49/0.59  fof(f339,plain,(
% 1.49/0.59    ~r1_tarski(k1_xboole_0,sK4) | spl7_42),
% 1.49/0.59    inference(avatar_component_clause,[],[f337])).
% 1.49/0.59  fof(f337,plain,(
% 1.49/0.59    spl7_42 <=> r1_tarski(k1_xboole_0,sK4)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).
% 1.49/0.59  fof(f32,plain,(
% 1.49/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f4])).
% 1.49/0.59  fof(f4,axiom,(
% 1.49/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.49/0.59  fof(f340,plain,(
% 1.49/0.59    ~spl7_42 | spl7_11 | ~spl7_28),
% 1.49/0.59    inference(avatar_split_clause,[],[f321,f198,f108,f337])).
% 1.49/0.59  fof(f108,plain,(
% 1.49/0.59    spl7_11 <=> r1_tarski(sK1,sK4)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.49/0.59  fof(f198,plain,(
% 1.49/0.59    spl7_28 <=> k1_xboole_0 = sK1),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 1.49/0.59  fof(f321,plain,(
% 1.49/0.59    ~r1_tarski(k1_xboole_0,sK4) | (spl7_11 | ~spl7_28)),
% 1.49/0.59    inference(backward_demodulation,[],[f110,f200])).
% 1.49/0.59  fof(f200,plain,(
% 1.49/0.59    k1_xboole_0 = sK1 | ~spl7_28),
% 1.49/0.59    inference(avatar_component_clause,[],[f198])).
% 1.49/0.59  fof(f110,plain,(
% 1.49/0.59    ~r1_tarski(sK1,sK4) | spl7_11),
% 1.49/0.59    inference(avatar_component_clause,[],[f108])).
% 1.49/0.59  fof(f317,plain,(
% 1.49/0.59    k1_xboole_0 != sK2 | sK2 != sK5 | v1_xboole_0(sK5) | ~v1_xboole_0(k1_xboole_0)),
% 1.49/0.59    introduced(theory_tautology_sat_conflict,[])).
% 1.49/0.59  fof(f316,plain,(
% 1.49/0.59    spl7_38),
% 1.49/0.59    inference(avatar_contradiction_clause,[],[f313])).
% 1.49/0.59  fof(f313,plain,(
% 1.49/0.59    $false | spl7_38),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f32,f306])).
% 1.49/0.59  fof(f306,plain,(
% 1.49/0.59    ~r1_tarski(k1_xboole_0,sK5) | spl7_38),
% 1.49/0.59    inference(avatar_component_clause,[],[f304])).
% 1.49/0.59  fof(f304,plain,(
% 1.49/0.59    spl7_38 <=> r1_tarski(k1_xboole_0,sK5)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 1.49/0.59  fof(f307,plain,(
% 1.49/0.59    ~spl7_38 | spl7_25 | ~spl7_29),
% 1.49/0.59    inference(avatar_split_clause,[],[f264,f202,f184,f304])).
% 1.49/0.59  fof(f184,plain,(
% 1.49/0.59    spl7_25 <=> r1_tarski(sK2,sK5)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 1.49/0.59  fof(f202,plain,(
% 1.49/0.59    spl7_29 <=> k1_xboole_0 = sK2),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 1.49/0.59  fof(f264,plain,(
% 1.49/0.59    ~r1_tarski(k1_xboole_0,sK5) | (spl7_25 | ~spl7_29)),
% 1.49/0.59    inference(backward_demodulation,[],[f186,f204])).
% 1.49/0.59  fof(f204,plain,(
% 1.49/0.59    k1_xboole_0 = sK2 | ~spl7_29),
% 1.49/0.59    inference(avatar_component_clause,[],[f202])).
% 1.49/0.59  fof(f186,plain,(
% 1.49/0.59    ~r1_tarski(sK2,sK5) | spl7_25),
% 1.49/0.59    inference(avatar_component_clause,[],[f184])).
% 1.49/0.59  fof(f260,plain,(
% 1.49/0.59    k1_xboole_0 != sK3 | v1_xboole_0(sK3) | ~v1_xboole_0(k1_xboole_0)),
% 1.49/0.59    introduced(theory_tautology_sat_conflict,[])).
% 1.49/0.59  fof(f259,plain,(
% 1.49/0.59    spl7_33),
% 1.49/0.59    inference(avatar_contradiction_clause,[],[f256])).
% 1.49/0.59  fof(f256,plain,(
% 1.49/0.59    $false | spl7_33),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f31,f254])).
% 1.49/0.59  fof(f254,plain,(
% 1.49/0.59    ~v1_xboole_0(k1_xboole_0) | spl7_33),
% 1.49/0.59    inference(avatar_component_clause,[],[f252])).
% 1.49/0.59  fof(f252,plain,(
% 1.49/0.59    spl7_33 <=> v1_xboole_0(k1_xboole_0)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 1.49/0.59  fof(f31,plain,(
% 1.49/0.59    v1_xboole_0(k1_xboole_0)),
% 1.49/0.59    inference(cnf_transformation,[],[f2])).
% 1.49/0.59  fof(f2,axiom,(
% 1.49/0.59    v1_xboole_0(k1_xboole_0)),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.49/0.59  fof(f249,plain,(
% 1.49/0.59    spl7_32 | ~spl7_10 | ~spl7_27),
% 1.49/0.59    inference(avatar_split_clause,[],[f236,f194,f103,f246])).
% 1.49/0.59  fof(f246,plain,(
% 1.49/0.59    spl7_32 <=> k1_xboole_0 = sK3),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 1.49/0.59  fof(f103,plain,(
% 1.49/0.59    spl7_10 <=> sK0 = sK3),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.49/0.59  fof(f194,plain,(
% 1.49/0.59    spl7_27 <=> k1_xboole_0 = sK0),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 1.49/0.59  fof(f236,plain,(
% 1.49/0.59    k1_xboole_0 = sK3 | (~spl7_10 | ~spl7_27)),
% 1.49/0.59    inference(forward_demodulation,[],[f105,f196])).
% 1.49/0.59  fof(f196,plain,(
% 1.49/0.59    k1_xboole_0 = sK0 | ~spl7_27),
% 1.49/0.59    inference(avatar_component_clause,[],[f194])).
% 1.49/0.59  fof(f105,plain,(
% 1.49/0.59    sK0 = sK3 | ~spl7_10),
% 1.49/0.59    inference(avatar_component_clause,[],[f103])).
% 1.49/0.59  fof(f235,plain,(
% 1.49/0.59    spl7_31),
% 1.49/0.59    inference(avatar_contradiction_clause,[],[f232])).
% 1.49/0.59  fof(f232,plain,(
% 1.49/0.59    $false | spl7_31),
% 1.49/0.59    inference(unit_resulting_resolution,[],[f32,f230])).
% 1.49/0.59  fof(f230,plain,(
% 1.49/0.59    ~r1_tarski(k1_xboole_0,sK3) | spl7_31),
% 1.49/0.59    inference(avatar_component_clause,[],[f228])).
% 1.49/0.59  fof(f228,plain,(
% 1.49/0.59    spl7_31 <=> r1_tarski(k1_xboole_0,sK3)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 1.49/0.59  fof(f231,plain,(
% 1.49/0.59    ~spl7_31 | spl7_9 | ~spl7_27),
% 1.49/0.59    inference(avatar_split_clause,[],[f218,f194,f99,f228])).
% 1.49/0.59  fof(f99,plain,(
% 1.49/0.59    spl7_9 <=> r1_tarski(sK0,sK3)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.49/0.59  fof(f218,plain,(
% 1.49/0.59    ~r1_tarski(k1_xboole_0,sK3) | (spl7_9 | ~spl7_27)),
% 1.49/0.59    inference(backward_demodulation,[],[f101,f196])).
% 1.49/0.59  fof(f101,plain,(
% 1.49/0.59    ~r1_tarski(sK0,sK3) | spl7_9),
% 1.49/0.59    inference(avatar_component_clause,[],[f99])).
% 1.49/0.59  fof(f213,plain,(
% 1.49/0.59    spl7_27 | spl7_28 | spl7_29 | ~spl7_8 | ~spl7_19 | spl7_22),
% 1.49/0.59    inference(avatar_split_clause,[],[f210,f169,f154,f94,f202,f198,f194])).
% 1.49/0.59  fof(f94,plain,(
% 1.49/0.59    spl7_8 <=> m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.49/0.59  fof(f154,plain,(
% 1.49/0.59    spl7_19 <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 1.49/0.59  fof(f169,plain,(
% 1.49/0.59    spl7_22 <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 1.49/0.59  fof(f210,plain,(
% 1.49/0.59    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | ~m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl7_22),
% 1.49/0.59    inference(superposition,[],[f171,f48])).
% 1.49/0.59  fof(f48,plain,(
% 1.49/0.59    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.49/0.59    inference(definition_unfolding,[],[f43,f39])).
% 1.49/0.59  fof(f39,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f6])).
% 1.49/0.59  fof(f6,axiom,(
% 1.49/0.59    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.49/0.59  fof(f43,plain,(
% 1.49/0.59    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.49/0.59    inference(cnf_transformation,[],[f16])).
% 1.49/0.59  fof(f16,plain,(
% 1.49/0.59    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.49/0.59    inference(ennf_transformation,[],[f8])).
% 1.49/0.59  fof(f8,axiom,(
% 1.49/0.59    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.49/0.59  fof(f171,plain,(
% 1.49/0.59    ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | spl7_22),
% 1.49/0.59    inference(avatar_component_clause,[],[f169])).
% 1.49/0.59  fof(f209,plain,(
% 1.49/0.59    spl7_27 | spl7_28 | spl7_29 | ~spl7_8 | ~spl7_13 | spl7_23),
% 1.49/0.59    inference(avatar_split_clause,[],[f208,f173,f120,f94,f202,f198,f194])).
% 1.49/0.59  fof(f120,plain,(
% 1.49/0.59    spl7_13 <=> r2_hidden(k2_mcart_1(sK6),sK5)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.49/0.59  fof(f173,plain,(
% 1.49/0.59    spl7_23 <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 1.49/0.59  fof(f208,plain,(
% 1.49/0.59    ~r2_hidden(k2_mcart_1(sK6),sK5) | ~m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl7_23),
% 1.49/0.59    inference(superposition,[],[f175,f47])).
% 1.49/0.59  fof(f47,plain,(
% 1.49/0.59    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.49/0.59    inference(definition_unfolding,[],[f44,f39])).
% 1.49/0.59  fof(f44,plain,(
% 1.49/0.59    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.49/0.59    inference(cnf_transformation,[],[f16])).
% 1.49/0.59  fof(f175,plain,(
% 1.49/0.59    ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | spl7_23),
% 1.49/0.59    inference(avatar_component_clause,[],[f173])).
% 1.49/0.59  fof(f205,plain,(
% 1.49/0.59    spl7_27 | spl7_28 | spl7_29 | ~spl7_8 | ~spl7_18 | spl7_21),
% 1.49/0.59    inference(avatar_split_clause,[],[f192,f165,f149,f94,f202,f198,f194])).
% 1.49/0.59  fof(f149,plain,(
% 1.49/0.59    spl7_18 <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 1.49/0.59  fof(f165,plain,(
% 1.49/0.59    spl7_21 <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 1.49/0.59  fof(f192,plain,(
% 1.49/0.59    ~r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | ~m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl7_21),
% 1.49/0.59    inference(superposition,[],[f167,f49])).
% 1.49/0.59  fof(f49,plain,(
% 1.49/0.59    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.49/0.59    inference(definition_unfolding,[],[f42,f39])).
% 1.49/0.59  fof(f42,plain,(
% 1.49/0.59    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.49/0.59    inference(cnf_transformation,[],[f16])).
% 1.49/0.59  fof(f167,plain,(
% 1.49/0.59    ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) | spl7_21),
% 1.49/0.59    inference(avatar_component_clause,[],[f165])).
% 1.49/0.59  fof(f191,plain,(
% 1.49/0.59    ~spl7_25 | spl7_26 | ~spl7_6),
% 1.49/0.59    inference(avatar_split_clause,[],[f87,f83,f188,f184])).
% 1.49/0.59  fof(f188,plain,(
% 1.49/0.59    spl7_26 <=> sK2 = sK5),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 1.49/0.59  fof(f83,plain,(
% 1.49/0.59    spl7_6 <=> r1_tarski(sK5,sK2)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.49/0.59  fof(f87,plain,(
% 1.49/0.59    sK2 = sK5 | ~r1_tarski(sK2,sK5) | ~spl7_6),
% 1.49/0.59    inference(resolution,[],[f85,f36])).
% 1.49/0.59  fof(f36,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f23])).
% 1.49/0.59  fof(f23,plain,(
% 1.49/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.49/0.59    inference(flattening,[],[f22])).
% 1.49/0.59  fof(f22,plain,(
% 1.49/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.49/0.59    inference(nnf_transformation,[],[f3])).
% 1.49/0.59  fof(f3,axiom,(
% 1.49/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.49/0.59  fof(f85,plain,(
% 1.49/0.59    r1_tarski(sK5,sK2) | ~spl7_6),
% 1.49/0.59    inference(avatar_component_clause,[],[f83])).
% 1.49/0.59  fof(f182,plain,(
% 1.49/0.59    ~spl7_24 | ~spl7_19),
% 1.49/0.59    inference(avatar_split_clause,[],[f177,f154,f179])).
% 1.49/0.59  fof(f179,plain,(
% 1.49/0.59    spl7_24 <=> v1_xboole_0(sK4)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 1.49/0.59  fof(f177,plain,(
% 1.49/0.59    ~v1_xboole_0(sK4) | ~spl7_19),
% 1.49/0.59    inference(resolution,[],[f156,f33])).
% 1.49/0.59  fof(f33,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f14])).
% 1.49/0.59  fof(f14,plain,(
% 1.49/0.59    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.49/0.59    inference(ennf_transformation,[],[f11])).
% 1.49/0.59  fof(f11,plain,(
% 1.49/0.59    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.49/0.59    inference(unused_predicate_definition_removal,[],[f1])).
% 1.49/0.59  fof(f1,axiom,(
% 1.49/0.59    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.49/0.59  fof(f156,plain,(
% 1.49/0.59    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | ~spl7_19),
% 1.49/0.59    inference(avatar_component_clause,[],[f154])).
% 1.49/0.59  fof(f176,plain,(
% 1.49/0.59    ~spl7_21 | ~spl7_22 | ~spl7_23),
% 1.49/0.59    inference(avatar_split_clause,[],[f30,f173,f169,f165])).
% 1.49/0.59  fof(f30,plain,(
% 1.49/0.59    ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)),
% 1.49/0.59    inference(cnf_transformation,[],[f21])).
% 1.49/0.59  fof(f21,plain,(
% 1.49/0.59    ((((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)) & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.49/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f13,f20,f19,f18,f17])).
% 1.49/0.59  fof(f17,plain,(
% 1.49/0.59    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0)))),
% 1.49/0.59    introduced(choice_axiom,[])).
% 1.49/0.59  fof(f18,plain,(
% 1.49/0.59    ? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(X4,k1_zfmisc_1(sK1))) => (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1)))),
% 1.49/0.59    introduced(choice_axiom,[])).
% 1.49/0.59  fof(f19,plain,(
% 1.49/0.59    ? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) => (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK2)))),
% 1.49/0.59    introduced(choice_axiom,[])).
% 1.49/0.59  fof(f20,plain,(
% 1.49/0.59    ? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) => ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)) & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)))),
% 1.49/0.59    introduced(choice_axiom,[])).
% 1.49/0.59  fof(f13,plain,(
% 1.49/0.59    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 1.49/0.59    inference(flattening,[],[f12])).
% 1.49/0.59  fof(f12,plain,(
% 1.49/0.59    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 1.49/0.59    inference(ennf_transformation,[],[f10])).
% 1.49/0.59  fof(f10,negated_conjecture,(
% 1.49/0.59    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 1.49/0.59    inference(negated_conjecture,[],[f9])).
% 1.49/0.59  fof(f9,conjecture,(
% 1.49/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).
% 1.49/0.59  fof(f163,plain,(
% 1.49/0.59    ~spl7_20 | ~spl7_18),
% 1.49/0.59    inference(avatar_split_clause,[],[f158,f149,f160])).
% 1.49/0.59  fof(f160,plain,(
% 1.49/0.59    spl7_20 <=> v1_xboole_0(sK3)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 1.49/0.59  fof(f158,plain,(
% 1.49/0.59    ~v1_xboole_0(sK3) | ~spl7_18),
% 1.49/0.59    inference(resolution,[],[f151,f33])).
% 1.49/0.59  fof(f151,plain,(
% 1.49/0.59    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | ~spl7_18),
% 1.49/0.59    inference(avatar_component_clause,[],[f149])).
% 1.49/0.59  fof(f157,plain,(
% 1.49/0.59    spl7_19 | ~spl7_15),
% 1.49/0.59    inference(avatar_split_clause,[],[f141,f131,f154])).
% 1.49/0.59  fof(f131,plain,(
% 1.49/0.59    spl7_15 <=> r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 1.49/0.59  fof(f141,plain,(
% 1.49/0.59    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | ~spl7_15),
% 1.49/0.59    inference(resolution,[],[f133,f41])).
% 1.49/0.59  fof(f41,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f15])).
% 1.49/0.59  fof(f15,plain,(
% 1.49/0.59    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.49/0.59    inference(ennf_transformation,[],[f7])).
% 1.49/0.59  fof(f7,axiom,(
% 1.49/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.49/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.49/0.59  fof(f133,plain,(
% 1.49/0.59    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) | ~spl7_15),
% 1.49/0.59    inference(avatar_component_clause,[],[f131])).
% 1.49/0.59  fof(f152,plain,(
% 1.49/0.59    spl7_18 | ~spl7_15),
% 1.49/0.59    inference(avatar_split_clause,[],[f140,f131,f149])).
% 1.49/0.59  fof(f140,plain,(
% 1.49/0.59    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | ~spl7_15),
% 1.49/0.59    inference(resolution,[],[f133,f40])).
% 1.49/0.59  fof(f40,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f15])).
% 1.49/0.59  fof(f134,plain,(
% 1.49/0.59    spl7_15 | ~spl7_7),
% 1.49/0.59    inference(avatar_split_clause,[],[f116,f89,f131])).
% 1.49/0.59  fof(f89,plain,(
% 1.49/0.59    spl7_7 <=> r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.49/0.59  fof(f116,plain,(
% 1.49/0.59    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) | ~spl7_7),
% 1.49/0.59    inference(resolution,[],[f91,f40])).
% 1.49/0.59  fof(f91,plain,(
% 1.49/0.59    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | ~spl7_7),
% 1.49/0.59    inference(avatar_component_clause,[],[f89])).
% 1.49/0.59  fof(f129,plain,(
% 1.49/0.59    ~spl7_14 | ~spl7_13),
% 1.49/0.59    inference(avatar_split_clause,[],[f124,f120,f126])).
% 1.49/0.59  fof(f126,plain,(
% 1.49/0.59    spl7_14 <=> v1_xboole_0(sK5)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 1.49/0.59  fof(f124,plain,(
% 1.49/0.59    ~v1_xboole_0(sK5) | ~spl7_13),
% 1.49/0.59    inference(resolution,[],[f122,f33])).
% 1.49/0.59  fof(f122,plain,(
% 1.49/0.59    r2_hidden(k2_mcart_1(sK6),sK5) | ~spl7_13),
% 1.49/0.59    inference(avatar_component_clause,[],[f120])).
% 1.49/0.59  fof(f123,plain,(
% 1.49/0.59    spl7_13 | ~spl7_7),
% 1.49/0.59    inference(avatar_split_clause,[],[f117,f89,f120])).
% 1.49/0.59  fof(f117,plain,(
% 1.49/0.59    r2_hidden(k2_mcart_1(sK6),sK5) | ~spl7_7),
% 1.49/0.59    inference(resolution,[],[f91,f41])).
% 1.49/0.59  fof(f115,plain,(
% 1.49/0.59    ~spl7_11 | spl7_12 | ~spl7_5),
% 1.49/0.59    inference(avatar_split_clause,[],[f80,f76,f112,f108])).
% 1.49/0.59  fof(f112,plain,(
% 1.49/0.59    spl7_12 <=> sK1 = sK4),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.49/0.59  fof(f76,plain,(
% 1.49/0.59    spl7_5 <=> r1_tarski(sK4,sK1)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.49/0.59  fof(f80,plain,(
% 1.49/0.59    sK1 = sK4 | ~r1_tarski(sK1,sK4) | ~spl7_5),
% 1.49/0.59    inference(resolution,[],[f78,f36])).
% 1.49/0.59  fof(f78,plain,(
% 1.49/0.59    r1_tarski(sK4,sK1) | ~spl7_5),
% 1.49/0.59    inference(avatar_component_clause,[],[f76])).
% 1.49/0.59  fof(f106,plain,(
% 1.49/0.59    ~spl7_9 | spl7_10 | ~spl7_4),
% 1.49/0.59    inference(avatar_split_clause,[],[f73,f69,f103,f99])).
% 1.49/0.59  fof(f69,plain,(
% 1.49/0.59    spl7_4 <=> r1_tarski(sK3,sK0)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.49/0.59  fof(f73,plain,(
% 1.49/0.59    sK0 = sK3 | ~r1_tarski(sK0,sK3) | ~spl7_4),
% 1.49/0.59    inference(resolution,[],[f71,f36])).
% 1.49/0.59  fof(f71,plain,(
% 1.49/0.59    r1_tarski(sK3,sK0) | ~spl7_4),
% 1.49/0.59    inference(avatar_component_clause,[],[f69])).
% 1.49/0.59  fof(f97,plain,(
% 1.49/0.59    spl7_8),
% 1.49/0.59    inference(avatar_split_clause,[],[f46,f94])).
% 1.49/0.59  fof(f46,plain,(
% 1.49/0.59    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.49/0.59    inference(definition_unfolding,[],[f28,f39])).
% 1.49/0.59  fof(f28,plain,(
% 1.49/0.59    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.49/0.59    inference(cnf_transformation,[],[f21])).
% 1.49/0.59  fof(f92,plain,(
% 1.49/0.59    spl7_7),
% 1.49/0.59    inference(avatar_split_clause,[],[f45,f89])).
% 1.49/0.59  fof(f45,plain,(
% 1.49/0.59    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 1.49/0.59    inference(definition_unfolding,[],[f29,f39])).
% 1.49/0.60  fof(f29,plain,(
% 1.49/0.60    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))),
% 1.49/0.60    inference(cnf_transformation,[],[f21])).
% 1.49/0.60  fof(f86,plain,(
% 1.49/0.60    spl7_6 | ~spl7_3),
% 1.49/0.60    inference(avatar_split_clause,[],[f81,f63,f83])).
% 1.49/0.60  fof(f63,plain,(
% 1.49/0.60    spl7_3 <=> m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 1.49/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.49/0.60  fof(f81,plain,(
% 1.49/0.60    r1_tarski(sK5,sK2) | ~spl7_3),
% 1.49/0.60    inference(resolution,[],[f65,f37])).
% 1.49/0.60  fof(f37,plain,(
% 1.49/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f24])).
% 1.49/0.60  fof(f24,plain,(
% 1.49/0.60    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.49/0.60    inference(nnf_transformation,[],[f5])).
% 1.49/0.60  fof(f5,axiom,(
% 1.49/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.49/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.49/0.60  fof(f65,plain,(
% 1.49/0.60    m1_subset_1(sK5,k1_zfmisc_1(sK2)) | ~spl7_3),
% 1.49/0.60    inference(avatar_component_clause,[],[f63])).
% 1.49/0.60  fof(f79,plain,(
% 1.49/0.60    spl7_5 | ~spl7_2),
% 1.49/0.60    inference(avatar_split_clause,[],[f74,f58,f76])).
% 1.49/0.60  fof(f58,plain,(
% 1.49/0.60    spl7_2 <=> m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 1.49/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.49/0.60  fof(f74,plain,(
% 1.49/0.60    r1_tarski(sK4,sK1) | ~spl7_2),
% 1.49/0.60    inference(resolution,[],[f60,f37])).
% 1.49/0.60  fof(f60,plain,(
% 1.49/0.60    m1_subset_1(sK4,k1_zfmisc_1(sK1)) | ~spl7_2),
% 1.49/0.60    inference(avatar_component_clause,[],[f58])).
% 1.49/0.60  fof(f72,plain,(
% 1.49/0.60    spl7_4 | ~spl7_1),
% 1.49/0.60    inference(avatar_split_clause,[],[f67,f53,f69])).
% 1.49/0.60  fof(f53,plain,(
% 1.49/0.60    spl7_1 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.49/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.49/0.60  fof(f67,plain,(
% 1.49/0.60    r1_tarski(sK3,sK0) | ~spl7_1),
% 1.49/0.60    inference(resolution,[],[f55,f37])).
% 1.49/0.60  fof(f55,plain,(
% 1.49/0.60    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl7_1),
% 1.49/0.60    inference(avatar_component_clause,[],[f53])).
% 1.49/0.60  fof(f66,plain,(
% 1.49/0.60    spl7_3),
% 1.49/0.60    inference(avatar_split_clause,[],[f27,f63])).
% 1.49/0.60  fof(f27,plain,(
% 1.49/0.60    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 1.49/0.60    inference(cnf_transformation,[],[f21])).
% 1.49/0.60  fof(f61,plain,(
% 1.49/0.60    spl7_2),
% 1.49/0.60    inference(avatar_split_clause,[],[f26,f58])).
% 1.49/0.60  fof(f26,plain,(
% 1.49/0.60    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 1.49/0.60    inference(cnf_transformation,[],[f21])).
% 1.49/0.60  fof(f56,plain,(
% 1.49/0.60    spl7_1),
% 1.49/0.60    inference(avatar_split_clause,[],[f25,f53])).
% 1.49/0.60  fof(f25,plain,(
% 1.49/0.60    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.49/0.60    inference(cnf_transformation,[],[f21])).
% 1.49/0.60  % SZS output end Proof for theBenchmark
% 1.49/0.60  % (26116)------------------------------
% 1.49/0.60  % (26116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.60  % (26116)Termination reason: Refutation
% 1.49/0.60  
% 1.49/0.60  % (26116)Memory used [KB]: 11001
% 1.49/0.60  % (26116)Time elapsed: 0.157 s
% 1.49/0.60  % (26116)------------------------------
% 1.49/0.60  % (26116)------------------------------
% 1.49/0.60  % (26105)Success in time 0.24 s
%------------------------------------------------------------------------------
