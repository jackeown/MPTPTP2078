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
% DateTime   : Thu Dec  3 12:58:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 213 expanded)
%              Number of leaves         :   30 (  82 expanded)
%              Depth                    :    9
%              Number of atoms          :  299 ( 579 expanded)
%              Number of equality atoms :  109 ( 232 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f233,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f68,f72,f76,f80,f103,f121,f170,f177,f184,f210,f219,f224,f231])).

fof(f231,plain,(
    ~ spl4_21 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl4_21 ),
    inference(trivial_inequality_removal,[],[f225])).

fof(f225,plain,
    ( sK2 != sK2
    | ~ spl4_21 ),
    inference(superposition,[],[f84,f222])).

fof(f222,plain,
    ( sK2 = k4_tarski(sK2,k2_mcart_1(sK2))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl4_21
  <=> sK2 = k4_tarski(sK2,k2_mcart_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f84,plain,(
    ! [X0,X1] : k4_tarski(X0,X1) != X0 ),
    inference(superposition,[],[f57,f47])).

fof(f47,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f57,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f224,plain,
    ( spl4_21
    | ~ spl4_1
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f223,f217,f59,f221])).

fof(f59,plain,
    ( spl4_1
  <=> sK2 = k1_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f217,plain,
    ( spl4_20
  <=> sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f223,plain,
    ( sK2 = k4_tarski(sK2,k2_mcart_1(sK2))
    | ~ spl4_1
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f218,f60])).

fof(f60,plain,
    ( sK2 = k1_mcart_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f218,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f217])).

fof(f219,plain,
    ( spl4_20
    | spl4_14
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f161,f66,f165,f217])).

fof(f165,plain,
    ( spl4_14
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f66,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f161,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ spl4_3 ),
    inference(resolution,[],[f159,f67])).

fof(f67,plain,
    ( m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f159,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,k2_zfmisc_1(X3,X4))
      | v1_xboole_0(k2_zfmisc_1(X3,X4))
      | k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 ) ),
    inference(resolution,[],[f91,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(resolution,[],[f49,f45])).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f210,plain,
    ( spl4_4
    | spl4_5
    | ~ spl4_9
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f209,f175,f119,f74,f70])).

fof(f70,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f74,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f119,plain,
    ( spl4_9
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f175,plain,
    ( spl4_16
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f209,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl4_9
    | ~ spl4_16 ),
    inference(duplicate_literal_removal,[],[f208])).

fof(f208,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl4_9
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f195,f120])).

fof(f120,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f119])).

fof(f195,plain,
    ( sK0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl4_16 ),
    inference(superposition,[],[f53,f176])).

fof(f176,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f175])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f184,plain,(
    ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | ~ spl4_15 ),
    inference(trivial_inequality_removal,[],[f180])).

fof(f180,plain,
    ( sK2 != sK2
    | ~ spl4_15 ),
    inference(superposition,[],[f83,f169])).

fof(f169,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl4_15
  <=> sK2 = k4_tarski(k1_mcart_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f83,plain,(
    ! [X0,X1] : k4_tarski(X0,X1) != X1 ),
    inference(superposition,[],[f56,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f13])).

fof(f56,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f177,plain,
    ( spl4_16
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f172,f165,f78,f175])).

fof(f78,plain,
    ( spl4_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f172,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(resolution,[],[f166,f81])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_6 ),
    inference(resolution,[],[f52,f79])).

fof(f79,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f166,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f165])).

fof(f170,plain,
    ( spl4_14
    | spl4_15
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f163,f66,f62,f168,f165])).

fof(f62,plain,
    ( spl4_2
  <=> sK2 = k2_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f163,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),sK2)
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f161,f63])).

fof(f63,plain,
    ( sK2 = k2_mcart_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f121,plain,
    ( spl4_9
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f114,f100,f78,f119])).

fof(f100,plain,
    ( spl4_8
  <=> ! [X3] :
        ( ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,X3))
        | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f114,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(superposition,[],[f88,f109])).

fof(f109,plain,
    ( ! [X3] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3)
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(resolution,[],[f107,f81])).

fof(f107,plain,
    ( ! [X0] : v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0))
    | ~ spl4_8 ),
    inference(resolution,[],[f101,f45])).

fof(f101,plain,
    ( ! [X3] :
        ( ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,X3))
        | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X3)) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f88,plain,
    ( ! [X0] : k1_xboole_0 = k1_relat_1(k2_zfmisc_1(k1_xboole_0,X0))
    | ~ spl4_6 ),
    inference(resolution,[],[f87,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ( ( r2_hidden(X3,X1)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_mcart_1)).

fof(f87,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k1_relat_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ spl4_6 ),
    inference(resolution,[],[f86,f46])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

fof(f86,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,k1_xboole_0)
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_6 ),
    inference(resolution,[],[f85,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f85,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f55,f79])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f103,plain,
    ( spl4_8
    | ~ spl4_6
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f94,f78,f78,f100])).

fof(f94,plain,
    ( ! [X3] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,X3))
        | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X3)) )
    | ~ spl4_6 ),
    inference(superposition,[],[f41,f88])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f80,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f40,f78])).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f76,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f36,f74])).

fof(f36,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( sK2 = k2_mcart_1(sK2)
      | sK2 = k1_mcart_1(sK2) )
    & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f32,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( k2_mcart_1(X2) = X2
              | k1_mcart_1(X2) = X2 )
            & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X2] :
        ( ( k2_mcart_1(X2) = X2
          | k1_mcart_1(X2) = X2 )
        & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
   => ( ( sK2 = k2_mcart_1(sK2)
        | sK2 = k1_mcart_1(sK2) )
      & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ! [X2] :
                ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
               => ( k2_mcart_1(X2) != X2
                  & k1_mcart_1(X2) != X2 ) )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => ( k2_mcart_1(X2) != X2
                & k1_mcart_1(X2) != X2 ) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).

fof(f72,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f37,f70])).

fof(f37,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f38,f66])).

fof(f38,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f39,f62,f59])).

fof(f39,plain,
    ( sK2 = k2_mcart_1(sK2)
    | sK2 = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:31:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (32194)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.46  % (32197)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.46  % (32198)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.46  % (32205)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (32205)Refutation not found, incomplete strategy% (32205)------------------------------
% 0.21/0.47  % (32205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (32205)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (32205)Memory used [KB]: 6140
% 0.21/0.47  % (32205)Time elapsed: 0.053 s
% 0.21/0.47  % (32205)------------------------------
% 0.21/0.47  % (32205)------------------------------
% 0.21/0.47  % (32203)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (32191)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (32191)Refutation not found, incomplete strategy% (32191)------------------------------
% 0.21/0.47  % (32191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (32191)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (32191)Memory used [KB]: 10618
% 0.21/0.47  % (32191)Time elapsed: 0.061 s
% 0.21/0.47  % (32191)------------------------------
% 0.21/0.47  % (32191)------------------------------
% 0.21/0.48  % (32196)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (32203)Refutation not found, incomplete strategy% (32203)------------------------------
% 0.21/0.48  % (32203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (32203)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (32203)Memory used [KB]: 1535
% 0.21/0.48  % (32203)Time elapsed: 0.076 s
% 0.21/0.48  % (32203)------------------------------
% 0.21/0.48  % (32203)------------------------------
% 0.21/0.49  % (32204)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (32195)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (32190)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (32190)Refutation not found, incomplete strategy% (32190)------------------------------
% 0.21/0.49  % (32190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (32190)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (32190)Memory used [KB]: 6140
% 0.21/0.49  % (32190)Time elapsed: 0.085 s
% 0.21/0.49  % (32190)------------------------------
% 0.21/0.49  % (32190)------------------------------
% 0.21/0.49  % (32192)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (32200)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (32200)Refutation not found, incomplete strategy% (32200)------------------------------
% 0.21/0.49  % (32200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (32200)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (32200)Memory used [KB]: 6140
% 0.21/0.49  % (32200)Time elapsed: 0.093 s
% 0.21/0.49  % (32200)------------------------------
% 0.21/0.49  % (32200)------------------------------
% 0.21/0.49  % (32192)Refutation not found, incomplete strategy% (32192)------------------------------
% 0.21/0.49  % (32192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (32192)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (32192)Memory used [KB]: 10618
% 0.21/0.49  % (32192)Time elapsed: 0.087 s
% 0.21/0.49  % (32192)------------------------------
% 0.21/0.49  % (32192)------------------------------
% 0.21/0.50  % (32193)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (32199)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (32193)Refutation not found, incomplete strategy% (32193)------------------------------
% 0.21/0.50  % (32193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (32193)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (32193)Memory used [KB]: 10618
% 0.21/0.50  % (32193)Time elapsed: 0.086 s
% 0.21/0.50  % (32193)------------------------------
% 0.21/0.50  % (32193)------------------------------
% 0.21/0.50  % (32207)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (32208)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (32202)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (32209)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (32196)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f233,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f64,f68,f72,f76,f80,f103,f121,f170,f177,f184,f210,f219,f224,f231])).
% 0.21/0.50  fof(f231,plain,(
% 0.21/0.50    ~spl4_21),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f230])).
% 0.21/0.50  fof(f230,plain,(
% 0.21/0.50    $false | ~spl4_21),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f225])).
% 0.21/0.50  fof(f225,plain,(
% 0.21/0.50    sK2 != sK2 | ~spl4_21),
% 0.21/0.50    inference(superposition,[],[f84,f222])).
% 0.21/0.50  fof(f222,plain,(
% 0.21/0.50    sK2 = k4_tarski(sK2,k2_mcart_1(sK2)) | ~spl4_21),
% 0.21/0.50    inference(avatar_component_clause,[],[f221])).
% 0.21/0.50  fof(f221,plain,(
% 0.21/0.50    spl4_21 <=> sK2 = k4_tarski(sK2,k2_mcart_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_tarski(X0,X1) != X0) )),
% 0.21/0.50    inference(superposition,[],[f57,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X2,X1] : (k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2))) )),
% 0.21/0.50    inference(equality_resolution,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.21/0.50  fof(f224,plain,(
% 0.21/0.50    spl4_21 | ~spl4_1 | ~spl4_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f223,f217,f59,f221])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    spl4_1 <=> sK2 = k1_mcart_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.50  fof(f217,plain,(
% 0.21/0.50    spl4_20 <=> sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.50  fof(f223,plain,(
% 0.21/0.50    sK2 = k4_tarski(sK2,k2_mcart_1(sK2)) | (~spl4_1 | ~spl4_20)),
% 0.21/0.50    inference(forward_demodulation,[],[f218,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    sK2 = k1_mcart_1(sK2) | ~spl4_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f59])).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | ~spl4_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f217])).
% 0.21/0.50  fof(f219,plain,(
% 0.21/0.50    spl4_20 | spl4_14 | ~spl4_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f161,f66,f165,f217])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    spl4_14 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    spl4_3 <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | ~spl4_3),
% 0.21/0.50    inference(resolution,[],[f159,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl4_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f66])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    ( ! [X4,X2,X3] : (~m1_subset_1(X2,k2_zfmisc_1(X3,X4)) | v1_xboole_0(k2_zfmisc_1(X3,X4)) | k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) )),
% 0.21/0.50    inference(resolution,[],[f91,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 0.21/0.50    inference(resolution,[],[f49,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.21/0.50  fof(f210,plain,(
% 0.21/0.50    spl4_4 | spl4_5 | ~spl4_9 | ~spl4_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f209,f175,f119,f74,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    spl4_4 <=> k1_xboole_0 = sK1),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    spl4_5 <=> k1_xboole_0 = sK0),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    spl4_9 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    spl4_16 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.50  fof(f209,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | (~spl4_9 | ~spl4_16)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f208])).
% 0.21/0.50  fof(f208,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl4_9 | ~spl4_16)),
% 0.21/0.50    inference(forward_demodulation,[],[f195,f120])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f119])).
% 0.21/0.50  fof(f195,plain,(
% 0.21/0.50    sK0 = k1_relat_1(k1_xboole_0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl4_16),
% 0.21/0.50    inference(superposition,[],[f53,f176])).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl4_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f175])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    ~spl4_15),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f183])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    $false | ~spl4_15),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f180])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    sK2 != sK2 | ~spl4_15),
% 0.21/0.50    inference(superposition,[],[f83,f169])).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    sK2 = k4_tarski(k1_mcart_1(sK2),sK2) | ~spl4_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f168])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    spl4_15 <=> sK2 = k4_tarski(k1_mcart_1(sK2),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_tarski(X0,X1) != X1) )),
% 0.21/0.50    inference(superposition,[],[f56,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 0.21/0.50    inference(equality_resolution,[],[f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    spl4_16 | ~spl4_6 | ~spl4_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f172,f165,f78,f175])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    spl4_6 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (~spl4_6 | ~spl4_14)),
% 0.21/0.50    inference(resolution,[],[f166,f81])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl4_6),
% 0.21/0.50    inference(resolution,[],[f52,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0) | ~spl4_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f78])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~spl4_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f165])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    spl4_14 | spl4_15 | ~spl4_2 | ~spl4_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f163,f66,f62,f168,f165])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    spl4_2 <=> sK2 = k2_mcart_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    sK2 = k4_tarski(k1_mcart_1(sK2),sK2) | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | (~spl4_2 | ~spl4_3)),
% 0.21/0.50    inference(forward_demodulation,[],[f161,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    sK2 = k2_mcart_1(sK2) | ~spl4_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f62])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    spl4_9 | ~spl4_6 | ~spl4_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f114,f100,f78,f119])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    spl4_8 <=> ! [X3] : (~v1_relat_1(k2_zfmisc_1(k1_xboole_0,X3)) | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X3)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl4_6 | ~spl4_8)),
% 0.21/0.50    inference(superposition,[],[f88,f109])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3)) ) | (~spl4_6 | ~spl4_8)),
% 0.21/0.50    inference(resolution,[],[f107,f81])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0))) ) | ~spl4_8),
% 0.21/0.50    inference(resolution,[],[f101,f45])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    ( ! [X3] : (~v1_relat_1(k2_zfmisc_1(k1_xboole_0,X3)) | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X3))) ) | ~spl4_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f100])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k1_relat_1(k2_zfmisc_1(k1_xboole_0,X0))) ) | ~spl4_6),
% 0.21/0.50    inference(resolution,[],[f87,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.50    inference(ennf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.50    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ((r2_hidden(X3,X1) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_mcart_1)).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(k2_zfmisc_1(k1_xboole_0,X1)))) ) | ~spl4_6),
% 0.21/0.50    inference(resolution,[],[f86,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X1,k1_xboole_0) | ~r2_hidden(X0,X1)) ) | ~spl4_6),
% 0.21/0.50    inference(resolution,[],[f85,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.50    inference(unused_predicate_definition_removal,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) ) | ~spl4_6),
% 0.21/0.50    inference(resolution,[],[f55,f79])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    spl4_8 | ~spl4_6 | ~spl4_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f94,f78,f78,f100])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X3] : (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0,X3)) | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X3))) ) | ~spl4_6),
% 0.21/0.50    inference(superposition,[],[f41,f88])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    spl4_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f40,f78])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ~spl4_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f36,f74])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    k1_xboole_0 != sK0),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ((sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)) & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f32,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ? [X0,X1] : (? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1))) => ((sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)) & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X0,X1] : (? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.50    inference(negated_conjecture,[],[f14])).
% 0.21/0.50  fof(f14,conjecture,(
% 0.21/0.50    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ~spl4_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f37,f70])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    k1_xboole_0 != sK1),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    spl4_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f38,f66])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    spl4_1 | spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f39,f62,f59])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (32196)------------------------------
% 0.21/0.50  % (32196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (32196)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (32196)Memory used [KB]: 10746
% 0.21/0.50  % (32196)Time elapsed: 0.049 s
% 0.21/0.50  % (32196)------------------------------
% 0.21/0.50  % (32196)------------------------------
% 0.21/0.50  % (32189)Success in time 0.146 s
%------------------------------------------------------------------------------
