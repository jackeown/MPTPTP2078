%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 137 expanded)
%              Number of leaves         :   28 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :  226 ( 288 expanded)
%              Number of equality atoms :   45 (  62 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f269,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f74,f79,f85,f91,f170,f183,f225,f247,f251,f256,f268])).

fof(f268,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f267,f105,f71,f66,f61])).

fof(f61,plain,
    ( spl3_1
  <=> k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f66,plain,
    ( spl3_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f71,plain,
    ( spl3_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f105,plain,
    ( spl3_8
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f267,plain,
    ( k1_xboole_0 = k3_relat_1(k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f266,f34])).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f266,plain,
    ( k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f265,f73])).

fof(f73,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f265,plain,
    ( k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f264,f68])).

fof(f68,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f264,plain,
    ( k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))
    | ~ spl3_8 ),
    inference(resolution,[],[f35,f107])).

fof(f107,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f256,plain,
    ( spl3_8
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f254,f167,f105])).

fof(f167,plain,
    ( spl3_16
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f254,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_16 ),
    inference(resolution,[],[f168,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f168,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f167])).

fof(f251,plain,
    ( ~ spl3_15
    | ~ spl3_21 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(resolution,[],[f246,f165])).

fof(f165,plain,
    ( ! [X0] : ~ r1_xboole_0(k1_xboole_0,X0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl3_15
  <=> ! [X0] : ~ r1_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f246,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl3_21
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f247,plain,
    ( spl3_21
    | ~ spl3_6
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f242,f181,f88,f244])).

fof(f88,plain,
    ( spl3_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f181,plain,
    ( spl3_18
  <=> ! [X2] :
        ( r1_xboole_0(k1_xboole_0,X2)
        | ~ v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f242,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_6
    | ~ spl3_18 ),
    inference(resolution,[],[f182,f90])).

fof(f90,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f182,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | r1_xboole_0(k1_xboole_0,X2) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f181])).

fof(f225,plain,
    ( spl3_1
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | spl3_1
    | ~ spl3_17 ),
    inference(trivial_inequality_removal,[],[f223])).

fof(f223,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl3_1
    | ~ spl3_17 ),
    inference(superposition,[],[f63,f192])).

fof(f192,plain,
    ( ! [X4] : k1_xboole_0 = X4
    | ~ spl3_17 ),
    inference(resolution,[],[f179,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f179,plain,
    ( ! [X3] : v1_xboole_0(X3)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl3_17
  <=> ! [X3] : v1_xboole_0(X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f63,plain,
    ( k1_xboole_0 != k3_relat_1(k1_xboole_0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f183,plain,
    ( spl3_17
    | spl3_18 ),
    inference(avatar_split_clause,[],[f176,f181,f178])).

fof(f176,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(k1_xboole_0,X2)
      | v1_xboole_0(X3)
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f171,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f171,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f158,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f158,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f154,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f154,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | r1_xboole_0(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f52,f59])).

fof(f59,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f170,plain,
    ( spl3_15
    | spl3_16 ),
    inference(avatar_split_clause,[],[f161,f167,f164])).

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f57,f55])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k1_xboole_0,X0) ),
    inference(definition_unfolding,[],[f33,f39])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k6_subset_1(X0,k6_subset_1(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f40,f39,f39])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f91,plain,
    ( spl3_6
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f86,f82,f76,f88])).

fof(f76,plain,
    ( spl3_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f82,plain,
    ( spl3_5
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f86,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f78,f84])).

fof(f84,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f78,plain,
    ( v1_xboole_0(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f85,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f80,f76,f82])).

fof(f80,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_4 ),
    inference(resolution,[],[f36,f78])).

fof(f79,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f53,f76])).

fof(f53,plain,(
    v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f74,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f31,f71])).

fof(f31,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f69,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f32,f66])).

fof(f32,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f30,f61])).

fof(f30,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f17])).

fof(f17,negated_conjecture,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (14042)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (14024)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (14034)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (14034)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f269,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f64,f69,f74,f79,f85,f91,f170,f183,f225,f247,f251,f256,f268])).
% 0.21/0.52  fof(f268,plain,(
% 0.21/0.52    spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f267,f105,f71,f66,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    spl3_1 <=> k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    spl3_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    spl3_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    spl3_8 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.52  fof(f267,plain,(
% 0.21/0.52    k1_xboole_0 = k3_relat_1(k1_xboole_0) | (~spl3_2 | ~spl3_3 | ~spl3_8)),
% 0.21/0.52    inference(forward_demodulation,[],[f266,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.52  fof(f266,plain,(
% 0.21/0.52    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl3_2 | ~spl3_3 | ~spl3_8)),
% 0.21/0.52    inference(forward_demodulation,[],[f265,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f71])).
% 0.21/0.52  fof(f265,plain,(
% 0.21/0.52    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl3_2 | ~spl3_8)),
% 0.21/0.52    inference(forward_demodulation,[],[f264,f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl3_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f66])).
% 0.21/0.52  fof(f264,plain,(
% 0.21/0.52    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) | ~spl3_8),
% 0.21/0.52    inference(resolution,[],[f35,f107])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    v1_relat_1(k1_xboole_0) | ~spl3_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f105])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.21/0.52  fof(f256,plain,(
% 0.21/0.52    spl3_8 | ~spl3_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f254,f167,f105])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    spl3_16 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.52  fof(f254,plain,(
% 0.21/0.52    v1_relat_1(k1_xboole_0) | ~spl3_16),
% 0.21/0.52    inference(resolution,[],[f168,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK0(X0),X0) | v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 0.21/0.52    inference(unused_predicate_definition_removal,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl3_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f167])).
% 0.21/0.52  fof(f251,plain,(
% 0.21/0.52    ~spl3_15 | ~spl3_21),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f250])).
% 0.21/0.52  fof(f250,plain,(
% 0.21/0.52    $false | (~spl3_15 | ~spl3_21)),
% 0.21/0.52    inference(resolution,[],[f246,f165])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_xboole_0(k1_xboole_0,X0)) ) | ~spl3_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f164])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    spl3_15 <=> ! [X0] : ~r1_xboole_0(k1_xboole_0,X0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.52  fof(f246,plain,(
% 0.21/0.52    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_21),
% 0.21/0.52    inference(avatar_component_clause,[],[f244])).
% 0.21/0.52  fof(f244,plain,(
% 0.21/0.52    spl3_21 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.52  fof(f247,plain,(
% 0.21/0.52    spl3_21 | ~spl3_6 | ~spl3_18),
% 0.21/0.52    inference(avatar_split_clause,[],[f242,f181,f88,f244])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    spl3_6 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    spl3_18 <=> ! [X2] : (r1_xboole_0(k1_xboole_0,X2) | ~v1_xboole_0(X2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.52  fof(f242,plain,(
% 0.21/0.52    r1_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl3_6 | ~spl3_18)),
% 0.21/0.52    inference(resolution,[],[f182,f90])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0) | ~spl3_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f88])).
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    ( ! [X2] : (~v1_xboole_0(X2) | r1_xboole_0(k1_xboole_0,X2)) ) | ~spl3_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f181])).
% 0.21/0.52  fof(f225,plain,(
% 0.21/0.52    spl3_1 | ~spl3_17),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f224])).
% 0.21/0.52  fof(f224,plain,(
% 0.21/0.52    $false | (spl3_1 | ~spl3_17)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f223])).
% 0.21/0.52  fof(f223,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | (spl3_1 | ~spl3_17)),
% 0.21/0.52    inference(superposition,[],[f63,f192])).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    ( ! [X4] : (k1_xboole_0 = X4) ) | ~spl3_17),
% 0.21/0.52    inference(resolution,[],[f179,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    ( ! [X3] : (v1_xboole_0(X3)) ) | ~spl3_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f178])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    spl3_17 <=> ! [X3] : v1_xboole_0(X3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    k1_xboole_0 != k3_relat_1(k1_xboole_0) | spl3_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f61])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    spl3_17 | spl3_18),
% 0.21/0.52    inference(avatar_split_clause,[],[f176,f181,f178])).
% 0.21/0.52  fof(f176,plain,(
% 0.21/0.52    ( ! [X2,X3] : (r1_xboole_0(k1_xboole_0,X2) | v1_xboole_0(X3) | ~v1_xboole_0(X2)) )),
% 0.21/0.52    inference(resolution,[],[f171,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.52  fof(f171,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(X1,X0) | r1_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(resolution,[],[f158,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(resolution,[],[f154,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_xboole_0,X1)) )),
% 0.21/0.52    inference(resolution,[],[f52,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_tarski(X1))) )),
% 0.21/0.52    inference(equality_resolution,[],[f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    spl3_15 | spl3_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f161,f167,f164])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(superposition,[],[f57,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f33,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,k6_subset_1(X0,k6_subset_1(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f45,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f40,f39,f39])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    spl3_6 | ~spl3_4 | ~spl3_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f86,f82,f76,f88])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    spl3_4 <=> v1_xboole_0(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    spl3_5 <=> k1_xboole_0 = sK2),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0) | (~spl3_4 | ~spl3_5)),
% 0.21/0.52    inference(backward_demodulation,[],[f78,f84])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | ~spl3_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f82])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    v1_xboole_0(sK2) | ~spl3_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f76])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    spl3_5 | ~spl3_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f80,f76,f82])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | ~spl3_4),
% 0.21/0.52    inference(resolution,[],[f36,f78])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    spl3_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f53,f76])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    v1_xboole_0(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ? [X0] : v1_xboole_0(X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    spl3_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f31,f71])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,axiom,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f32,f66])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ~spl3_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f30,f61])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(flattening,[],[f17])).
% 0.21/0.52  fof(f17,negated_conjecture,(
% 0.21/0.52    ~k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(negated_conjecture,[],[f16])).
% 0.21/0.52  fof(f16,conjecture,(
% 0.21/0.52    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (14034)------------------------------
% 0.21/0.52  % (14034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14034)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (14034)Memory used [KB]: 10746
% 0.21/0.52  % (14034)Time elapsed: 0.111 s
% 0.21/0.52  % (14034)------------------------------
% 0.21/0.52  % (14034)------------------------------
% 0.21/0.52  % (14016)Success in time 0.169 s
%------------------------------------------------------------------------------
