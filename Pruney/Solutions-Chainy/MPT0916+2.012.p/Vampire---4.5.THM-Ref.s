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
% DateTime   : Thu Dec  3 12:59:39 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 279 expanded)
%              Number of leaves         :   40 ( 119 expanded)
%              Depth                    :    8
%              Number of atoms          :  350 ( 770 expanded)
%              Number of equality atoms :   62 ( 106 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f439,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f61,f66,f71,f76,f89,f147,f159,f166,f185,f298,f301,f304,f330,f331,f332,f343,f348,f354,f355,f360,f374,f376,f379,f387,f420,f437,f438])).

fof(f438,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) != k1_mcart_1(k1_mcart_1(sK6))
    | r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f437,plain,
    ( ~ spl8_34
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f436,f345,f320])).

fof(f320,plain,
    ( spl8_34
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f345,plain,
    ( spl8_36
  <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f436,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl8_36 ),
    inference(resolution,[],[f347,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f347,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f345])).

fof(f420,plain,
    ( ~ spl8_38
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f419,f340,f371])).

fof(f371,plain,
    ( spl8_38
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f340,plain,
    ( spl8_35
  <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f419,plain,
    ( ~ v1_xboole_0(sK4)
    | ~ spl8_35 ),
    inference(resolution,[],[f342,f31])).

fof(f342,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f340])).

fof(f387,plain,
    ( spl8_23
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f386,f216,f206])).

fof(f206,plain,
    ( spl8_23
  <=> r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f216,plain,
    ( spl8_25
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f386,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl8_25 ),
    inference(resolution,[],[f218,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f218,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f216])).

fof(f379,plain,
    ( spl8_25
    | ~ spl8_1
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f199,f173,f53,f216])).

fof(f53,plain,
    ( spl8_1
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f173,plain,
    ( spl8_18
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f199,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_1
    | ~ spl8_18 ),
    inference(backward_demodulation,[],[f55,f175])).

fof(f175,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f173])).

fof(f55,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f376,plain,
    ( spl8_34
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f317,f206,f320])).

fof(f317,plain,
    ( v1_xboole_0(sK3)
    | ~ spl8_23 ),
    inference(resolution,[],[f208,f139])).

fof(f139,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f129,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f129,plain,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    inference(resolution,[],[f127,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f127,plain,(
    ! [X2] : r1_xboole_0(k1_xboole_0,X2) ),
    inference(resolution,[],[f41,f30])).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f208,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f206])).

fof(f374,plain,
    ( spl8_38
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f368,f281,f371])).

fof(f281,plain,
    ( spl8_32
  <=> r1_tarski(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f368,plain,
    ( v1_xboole_0(sK4)
    | ~ spl8_32 ),
    inference(resolution,[],[f283,f139])).

fof(f283,plain,
    ( r1_tarski(sK4,k1_xboole_0)
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f281])).

fof(f360,plain,
    ( spl8_32
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f359,f286,f281])).

fof(f286,plain,
    ( spl8_33
  <=> m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f359,plain,
    ( r1_tarski(sK4,k1_xboole_0)
    | ~ spl8_33 ),
    inference(resolution,[],[f288,f38])).

fof(f288,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f286])).

fof(f355,plain,
    ( spl8_33
    | ~ spl8_2
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f269,f181,f58,f286])).

fof(f58,plain,
    ( spl8_2
  <=> m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f181,plain,
    ( spl8_20
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f269,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_2
    | ~ spl8_20 ),
    inference(backward_demodulation,[],[f60,f183])).

fof(f183,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f181])).

fof(f60,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f354,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(k1_mcart_1(sK6))
    | r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f348,plain,
    ( spl8_36
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f336,f144,f345])).

fof(f144,plain,
    ( spl8_14
  <=> r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f336,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ spl8_14 ),
    inference(resolution,[],[f146,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f146,plain,
    ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f144])).

fof(f343,plain,
    ( spl8_35
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f335,f144,f340])).

fof(f335,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | ~ spl8_14 ),
    inference(resolution,[],[f146,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f332,plain,
    ( spl8_17
    | spl8_18
    | spl8_19
    | spl8_20
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f329,f73,f181,f177,f173,f169])).

fof(f169,plain,
    ( spl8_17
  <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f177,plain,
    ( spl8_19
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f73,plain,
    ( spl8_5
  <=> m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f329,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)
    | ~ spl8_5 ),
    inference(resolution,[],[f75,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(definition_unfolding,[],[f46,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f75,plain,
    ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f331,plain,
    ( spl8_21
    | spl8_18
    | spl8_19
    | spl8_20
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f328,f73,f181,f177,f173,f192])).

fof(f192,plain,
    ( spl8_21
  <=> k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f328,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | ~ spl8_5 ),
    inference(resolution,[],[f75,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) ) ),
    inference(definition_unfolding,[],[f45,f39])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f330,plain,
    ( spl8_29
    | spl8_18
    | spl8_19
    | spl8_20
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f327,f73,f181,f177,f173,f262])).

fof(f262,plain,
    ( spl8_29
  <=> k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f327,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | ~ spl8_5 ),
    inference(resolution,[],[f75,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(definition_unfolding,[],[f44,f39])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f304,plain,
    ( spl8_16
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f302,f236,f163])).

fof(f163,plain,
    ( spl8_16
  <=> v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f236,plain,
    ( spl8_27
  <=> r1_tarski(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f302,plain,
    ( v1_xboole_0(sK5)
    | ~ spl8_27 ),
    inference(resolution,[],[f238,f139])).

fof(f238,plain,
    ( r1_tarski(sK5,k1_xboole_0)
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f236])).

fof(f301,plain,
    ( spl8_27
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f300,f241,f236])).

fof(f241,plain,
    ( spl8_28
  <=> m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f300,plain,
    ( r1_tarski(sK5,k1_xboole_0)
    | ~ spl8_28 ),
    inference(resolution,[],[f243,f38])).

fof(f243,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f241])).

fof(f298,plain,
    ( spl8_28
    | ~ spl8_3
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f296,f177,f63,f241])).

fof(f63,plain,
    ( spl8_3
  <=> m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f296,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_3
    | ~ spl8_19 ),
    inference(backward_demodulation,[],[f65,f179])).

fof(f179,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f177])).

fof(f65,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f185,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(sK6)
    | r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | ~ r2_hidden(k2_mcart_1(sK6),sK5) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f166,plain,
    ( ~ spl8_16
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f161,f156,f163])).

fof(f156,plain,
    ( spl8_15
  <=> r2_hidden(k2_mcart_1(sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f161,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ spl8_15 ),
    inference(resolution,[],[f158,f31])).

fof(f158,plain,
    ( r2_hidden(k2_mcart_1(sK6),sK5)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f156])).

fof(f159,plain,
    ( spl8_15
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f153,f68,f156])).

fof(f68,plain,
    ( spl8_4
  <=> r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f153,plain,
    ( r2_hidden(k2_mcart_1(sK6),sK5)
    | ~ spl8_4 ),
    inference(resolution,[],[f43,f70])).

fof(f70,plain,
    ( r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f147,plain,
    ( spl8_14
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f141,f68,f144])).

fof(f141,plain,
    ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))
    | ~ spl8_4 ),
    inference(resolution,[],[f42,f70])).

fof(f89,plain,
    ( ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f24,f86,f82,f78])).

fof(f78,plain,
    ( spl8_6
  <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f82,plain,
    ( spl8_7
  <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f86,plain,
    ( spl8_8
  <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f24,plain,
    ( ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_mcart_1)).

fof(f76,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f48,f73])).

fof(f48,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f25,f39])).

fof(f25,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f47,f68])).

fof(f47,plain,(
    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f26,f39])).

fof(f26,plain,(
    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f15])).

fof(f66,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f61,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f28,f58])).

fof(f28,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f29,f53])).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:54:30 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.51  % (5833)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.51  % (5825)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.23/0.51  % (5816)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.51  % (5818)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.23/0.51  % (5810)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.52  % (5811)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.52  % (5815)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.52  % (5833)Refutation not found, incomplete strategy% (5833)------------------------------
% 0.23/0.52  % (5833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (5838)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.23/0.52  % (5812)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.52  % (5822)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.23/0.52  % (5833)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (5833)Memory used [KB]: 10874
% 0.23/0.52  % (5833)Time elapsed: 0.063 s
% 0.23/0.52  % (5833)------------------------------
% 0.23/0.52  % (5833)------------------------------
% 0.23/0.52  % (5821)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.23/0.52  % (5821)Refutation not found, incomplete strategy% (5821)------------------------------
% 0.23/0.52  % (5821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (5830)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.23/0.53  % (5839)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.23/0.53  % (5821)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (5821)Memory used [KB]: 10746
% 0.23/0.53  % (5821)Time elapsed: 0.101 s
% 0.23/0.53  % (5821)------------------------------
% 0.23/0.53  % (5821)------------------------------
% 0.23/0.53  % (5814)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.23/0.53  % (5832)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.23/0.53  % (5813)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.53  % (5819)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.23/0.54  % (5826)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.23/0.54  % (5836)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.23/0.54  % (5824)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.23/0.54  % (5812)Refutation not found, incomplete strategy% (5812)------------------------------
% 0.23/0.54  % (5812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (5812)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (5812)Memory used [KB]: 10746
% 0.23/0.54  % (5812)Time elapsed: 0.127 s
% 0.23/0.54  % (5812)------------------------------
% 0.23/0.54  % (5812)------------------------------
% 0.23/0.54  % (5829)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.23/0.55  % (5827)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.23/0.55  % (5841)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.39/0.55  % (5819)Refutation not found, incomplete strategy% (5819)------------------------------
% 1.39/0.55  % (5819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (5819)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (5819)Memory used [KB]: 10746
% 1.39/0.55  % (5819)Time elapsed: 0.143 s
% 1.39/0.55  % (5819)------------------------------
% 1.39/0.55  % (5819)------------------------------
% 1.39/0.55  % (5837)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.39/0.55  % (5831)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.39/0.56  % (5827)Refutation found. Thanks to Tanya!
% 1.39/0.56  % SZS status Theorem for theBenchmark
% 1.39/0.56  % SZS output start Proof for theBenchmark
% 1.39/0.56  fof(f439,plain,(
% 1.39/0.56    $false),
% 1.39/0.56    inference(avatar_sat_refutation,[],[f56,f61,f66,f71,f76,f89,f147,f159,f166,f185,f298,f301,f304,f330,f331,f332,f343,f348,f354,f355,f360,f374,f376,f379,f387,f420,f437,f438])).
% 1.39/0.56  fof(f438,plain,(
% 1.39/0.56    k5_mcart_1(sK0,sK1,sK2,sK6) != k1_mcart_1(k1_mcart_1(sK6)) | r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) | ~r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)),
% 1.39/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.39/0.56  fof(f437,plain,(
% 1.39/0.56    ~spl8_34 | ~spl8_36),
% 1.39/0.56    inference(avatar_split_clause,[],[f436,f345,f320])).
% 1.39/0.56  fof(f320,plain,(
% 1.39/0.56    spl8_34 <=> v1_xboole_0(sK3)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).
% 1.39/0.56  fof(f345,plain,(
% 1.39/0.56    spl8_36 <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 1.39/0.56  fof(f436,plain,(
% 1.39/0.56    ~v1_xboole_0(sK3) | ~spl8_36),
% 1.39/0.56    inference(resolution,[],[f347,f31])).
% 1.39/0.56  fof(f31,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f16])).
% 1.39/0.56  fof(f16,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.39/0.56    inference(ennf_transformation,[],[f13])).
% 1.39/0.56  fof(f13,plain,(
% 1.39/0.56    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.39/0.56    inference(unused_predicate_definition_removal,[],[f1])).
% 1.39/0.56  fof(f1,axiom,(
% 1.39/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.39/0.56  fof(f347,plain,(
% 1.39/0.56    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | ~spl8_36),
% 1.39/0.56    inference(avatar_component_clause,[],[f345])).
% 1.39/0.56  fof(f420,plain,(
% 1.39/0.56    ~spl8_38 | ~spl8_35),
% 1.39/0.56    inference(avatar_split_clause,[],[f419,f340,f371])).
% 1.39/0.56  fof(f371,plain,(
% 1.39/0.56    spl8_38 <=> v1_xboole_0(sK4)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 1.39/0.56  fof(f340,plain,(
% 1.39/0.56    spl8_35 <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 1.39/0.56  fof(f419,plain,(
% 1.39/0.56    ~v1_xboole_0(sK4) | ~spl8_35),
% 1.39/0.56    inference(resolution,[],[f342,f31])).
% 1.39/0.56  fof(f342,plain,(
% 1.39/0.56    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | ~spl8_35),
% 1.39/0.56    inference(avatar_component_clause,[],[f340])).
% 1.39/0.56  fof(f387,plain,(
% 1.39/0.56    spl8_23 | ~spl8_25),
% 1.39/0.56    inference(avatar_split_clause,[],[f386,f216,f206])).
% 1.39/0.56  fof(f206,plain,(
% 1.39/0.56    spl8_23 <=> r1_tarski(sK3,k1_xboole_0)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 1.39/0.56  fof(f216,plain,(
% 1.39/0.56    spl8_25 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 1.39/0.56  fof(f386,plain,(
% 1.39/0.56    r1_tarski(sK3,k1_xboole_0) | ~spl8_25),
% 1.39/0.56    inference(resolution,[],[f218,f38])).
% 1.39/0.56  fof(f38,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f7])).
% 1.39/0.56  fof(f7,axiom,(
% 1.39/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.39/0.56  fof(f218,plain,(
% 1.39/0.56    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl8_25),
% 1.39/0.56    inference(avatar_component_clause,[],[f216])).
% 1.39/0.56  fof(f379,plain,(
% 1.39/0.56    spl8_25 | ~spl8_1 | ~spl8_18),
% 1.39/0.56    inference(avatar_split_clause,[],[f199,f173,f53,f216])).
% 1.39/0.56  fof(f53,plain,(
% 1.39/0.56    spl8_1 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.39/0.56  fof(f173,plain,(
% 1.39/0.56    spl8_18 <=> k1_xboole_0 = sK0),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 1.39/0.56  fof(f199,plain,(
% 1.39/0.56    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl8_1 | ~spl8_18)),
% 1.39/0.56    inference(backward_demodulation,[],[f55,f175])).
% 1.39/0.56  fof(f175,plain,(
% 1.39/0.56    k1_xboole_0 = sK0 | ~spl8_18),
% 1.39/0.56    inference(avatar_component_clause,[],[f173])).
% 1.39/0.56  fof(f55,plain,(
% 1.39/0.56    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl8_1),
% 1.39/0.56    inference(avatar_component_clause,[],[f53])).
% 1.39/0.56  fof(f376,plain,(
% 1.39/0.56    spl8_34 | ~spl8_23),
% 1.39/0.56    inference(avatar_split_clause,[],[f317,f206,f320])).
% 1.39/0.56  fof(f317,plain,(
% 1.39/0.56    v1_xboole_0(sK3) | ~spl8_23),
% 1.39/0.56    inference(resolution,[],[f208,f139])).
% 1.39/0.56  fof(f139,plain,(
% 1.39/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)) )),
% 1.39/0.56    inference(resolution,[],[f129,f32])).
% 1.39/0.56  fof(f32,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f18])).
% 1.39/0.56  fof(f18,plain,(
% 1.39/0.56    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.39/0.56    inference(flattening,[],[f17])).
% 1.39/0.56  fof(f17,plain,(
% 1.39/0.56    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.39/0.56    inference(ennf_transformation,[],[f6])).
% 1.39/0.56  fof(f6,axiom,(
% 1.39/0.56    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 1.39/0.56  fof(f129,plain,(
% 1.39/0.56    ( ! [X1] : (r1_xboole_0(X1,k1_xboole_0)) )),
% 1.39/0.56    inference(resolution,[],[f127,f33])).
% 1.39/0.56  fof(f33,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f19])).
% 1.39/0.56  fof(f19,plain,(
% 1.39/0.56    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.39/0.56    inference(ennf_transformation,[],[f3])).
% 1.39/0.56  fof(f3,axiom,(
% 1.39/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.39/0.56  fof(f127,plain,(
% 1.39/0.56    ( ! [X2] : (r1_xboole_0(k1_xboole_0,X2)) )),
% 1.39/0.56    inference(resolution,[],[f41,f30])).
% 1.39/0.56  fof(f30,plain,(
% 1.39/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f5])).
% 1.39/0.56  fof(f5,axiom,(
% 1.39/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.39/0.56  fof(f41,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f21])).
% 1.39/0.56  fof(f21,plain,(
% 1.39/0.56    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.39/0.56    inference(ennf_transformation,[],[f4])).
% 1.39/0.56  fof(f4,axiom,(
% 1.39/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.39/0.56  fof(f208,plain,(
% 1.39/0.56    r1_tarski(sK3,k1_xboole_0) | ~spl8_23),
% 1.39/0.56    inference(avatar_component_clause,[],[f206])).
% 1.39/0.56  fof(f374,plain,(
% 1.39/0.56    spl8_38 | ~spl8_32),
% 1.39/0.56    inference(avatar_split_clause,[],[f368,f281,f371])).
% 1.39/0.56  fof(f281,plain,(
% 1.39/0.56    spl8_32 <=> r1_tarski(sK4,k1_xboole_0)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 1.39/0.56  fof(f368,plain,(
% 1.39/0.56    v1_xboole_0(sK4) | ~spl8_32),
% 1.39/0.56    inference(resolution,[],[f283,f139])).
% 1.39/0.56  fof(f283,plain,(
% 1.39/0.56    r1_tarski(sK4,k1_xboole_0) | ~spl8_32),
% 1.39/0.56    inference(avatar_component_clause,[],[f281])).
% 1.39/0.56  fof(f360,plain,(
% 1.39/0.56    spl8_32 | ~spl8_33),
% 1.39/0.56    inference(avatar_split_clause,[],[f359,f286,f281])).
% 1.39/0.56  fof(f286,plain,(
% 1.39/0.56    spl8_33 <=> m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 1.39/0.56  fof(f359,plain,(
% 1.39/0.56    r1_tarski(sK4,k1_xboole_0) | ~spl8_33),
% 1.39/0.56    inference(resolution,[],[f288,f38])).
% 1.39/0.56  fof(f288,plain,(
% 1.39/0.56    m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) | ~spl8_33),
% 1.39/0.56    inference(avatar_component_clause,[],[f286])).
% 1.39/0.56  fof(f355,plain,(
% 1.39/0.56    spl8_33 | ~spl8_2 | ~spl8_20),
% 1.39/0.56    inference(avatar_split_clause,[],[f269,f181,f58,f286])).
% 1.39/0.56  fof(f58,plain,(
% 1.39/0.56    spl8_2 <=> m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.39/0.56  fof(f181,plain,(
% 1.39/0.56    spl8_20 <=> k1_xboole_0 = sK1),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 1.39/0.56  fof(f269,plain,(
% 1.39/0.56    m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) | (~spl8_2 | ~spl8_20)),
% 1.39/0.56    inference(backward_demodulation,[],[f60,f183])).
% 1.39/0.56  fof(f183,plain,(
% 1.39/0.56    k1_xboole_0 = sK1 | ~spl8_20),
% 1.39/0.56    inference(avatar_component_clause,[],[f181])).
% 1.39/0.56  fof(f60,plain,(
% 1.39/0.56    m1_subset_1(sK4,k1_zfmisc_1(sK1)) | ~spl8_2),
% 1.39/0.56    inference(avatar_component_clause,[],[f58])).
% 1.39/0.56  fof(f354,plain,(
% 1.39/0.56    k6_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(k1_mcart_1(sK6)) | r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)),
% 1.39/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.39/0.56  fof(f348,plain,(
% 1.39/0.56    spl8_36 | ~spl8_14),
% 1.39/0.56    inference(avatar_split_clause,[],[f336,f144,f345])).
% 1.39/0.56  fof(f144,plain,(
% 1.39/0.56    spl8_14 <=> r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.39/0.56  fof(f336,plain,(
% 1.39/0.56    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | ~spl8_14),
% 1.39/0.56    inference(resolution,[],[f146,f42])).
% 1.39/0.56  fof(f42,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f22])).
% 1.39/0.56  fof(f22,plain,(
% 1.39/0.56    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.39/0.56    inference(ennf_transformation,[],[f9])).
% 1.39/0.56  fof(f9,axiom,(
% 1.39/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.39/0.56  fof(f146,plain,(
% 1.39/0.56    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) | ~spl8_14),
% 1.39/0.56    inference(avatar_component_clause,[],[f144])).
% 1.39/0.56  fof(f343,plain,(
% 1.39/0.56    spl8_35 | ~spl8_14),
% 1.39/0.56    inference(avatar_split_clause,[],[f335,f144,f340])).
% 1.39/0.56  fof(f335,plain,(
% 1.39/0.56    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | ~spl8_14),
% 1.39/0.56    inference(resolution,[],[f146,f43])).
% 1.39/0.56  fof(f43,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f22])).
% 1.39/0.56  fof(f332,plain,(
% 1.39/0.56    spl8_17 | spl8_18 | spl8_19 | spl8_20 | ~spl8_5),
% 1.39/0.56    inference(avatar_split_clause,[],[f329,f73,f181,f177,f173,f169])).
% 1.39/0.56  fof(f169,plain,(
% 1.39/0.56    spl8_17 <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 1.39/0.56  fof(f177,plain,(
% 1.39/0.56    spl8_19 <=> k1_xboole_0 = sK2),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 1.39/0.56  fof(f73,plain,(
% 1.39/0.56    spl8_5 <=> m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.39/0.56  fof(f329,plain,(
% 1.39/0.56    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) | ~spl8_5),
% 1.39/0.56    inference(resolution,[],[f75,f49])).
% 1.39/0.56  fof(f49,plain,(
% 1.39/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 1.39/0.56    inference(definition_unfolding,[],[f46,f39])).
% 1.39/0.56  fof(f39,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f8])).
% 1.39/0.56  fof(f8,axiom,(
% 1.39/0.56    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.39/0.56  fof(f46,plain,(
% 1.39/0.56    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f23])).
% 1.39/0.56  fof(f23,plain,(
% 1.39/0.56    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.39/0.56    inference(ennf_transformation,[],[f10])).
% 1.39/0.56  fof(f10,axiom,(
% 1.39/0.56    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.39/0.56  fof(f75,plain,(
% 1.39/0.56    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl8_5),
% 1.39/0.56    inference(avatar_component_clause,[],[f73])).
% 1.39/0.56  fof(f331,plain,(
% 1.39/0.56    spl8_21 | spl8_18 | spl8_19 | spl8_20 | ~spl8_5),
% 1.39/0.56    inference(avatar_split_clause,[],[f328,f73,f181,f177,f173,f192])).
% 1.39/0.56  fof(f192,plain,(
% 1.39/0.56    spl8_21 <=> k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 1.39/0.56  fof(f328,plain,(
% 1.39/0.56    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) | ~spl8_5),
% 1.39/0.56    inference(resolution,[],[f75,f50])).
% 1.39/0.56  fof(f50,plain,(
% 1.39/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))) )),
% 1.39/0.56    inference(definition_unfolding,[],[f45,f39])).
% 1.39/0.56  fof(f45,plain,(
% 1.39/0.56    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))) )),
% 1.39/0.56    inference(cnf_transformation,[],[f23])).
% 1.39/0.56  fof(f330,plain,(
% 1.39/0.56    spl8_29 | spl8_18 | spl8_19 | spl8_20 | ~spl8_5),
% 1.39/0.56    inference(avatar_split_clause,[],[f327,f73,f181,f177,f173,f262])).
% 1.39/0.56  fof(f262,plain,(
% 1.39/0.56    spl8_29 <=> k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 1.39/0.56  fof(f327,plain,(
% 1.39/0.56    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) | ~spl8_5),
% 1.39/0.56    inference(resolution,[],[f75,f51])).
% 1.39/0.56  fof(f51,plain,(
% 1.39/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) )),
% 1.39/0.56    inference(definition_unfolding,[],[f44,f39])).
% 1.39/0.56  fof(f44,plain,(
% 1.39/0.56    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) )),
% 1.39/0.56    inference(cnf_transformation,[],[f23])).
% 1.39/0.56  fof(f304,plain,(
% 1.39/0.56    spl8_16 | ~spl8_27),
% 1.39/0.56    inference(avatar_split_clause,[],[f302,f236,f163])).
% 1.39/0.56  fof(f163,plain,(
% 1.39/0.56    spl8_16 <=> v1_xboole_0(sK5)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 1.39/0.56  fof(f236,plain,(
% 1.39/0.56    spl8_27 <=> r1_tarski(sK5,k1_xboole_0)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 1.39/0.56  fof(f302,plain,(
% 1.39/0.56    v1_xboole_0(sK5) | ~spl8_27),
% 1.39/0.56    inference(resolution,[],[f238,f139])).
% 1.39/0.56  fof(f238,plain,(
% 1.39/0.56    r1_tarski(sK5,k1_xboole_0) | ~spl8_27),
% 1.39/0.56    inference(avatar_component_clause,[],[f236])).
% 1.39/0.56  fof(f301,plain,(
% 1.39/0.56    spl8_27 | ~spl8_28),
% 1.39/0.56    inference(avatar_split_clause,[],[f300,f241,f236])).
% 1.39/0.56  fof(f241,plain,(
% 1.39/0.56    spl8_28 <=> m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 1.39/0.56  fof(f300,plain,(
% 1.39/0.56    r1_tarski(sK5,k1_xboole_0) | ~spl8_28),
% 1.39/0.56    inference(resolution,[],[f243,f38])).
% 1.39/0.56  fof(f243,plain,(
% 1.39/0.56    m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) | ~spl8_28),
% 1.39/0.56    inference(avatar_component_clause,[],[f241])).
% 1.39/0.56  fof(f298,plain,(
% 1.39/0.56    spl8_28 | ~spl8_3 | ~spl8_19),
% 1.39/0.56    inference(avatar_split_clause,[],[f296,f177,f63,f241])).
% 1.39/0.56  fof(f63,plain,(
% 1.39/0.56    spl8_3 <=> m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.39/0.56  fof(f296,plain,(
% 1.39/0.56    m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) | (~spl8_3 | ~spl8_19)),
% 1.39/0.56    inference(backward_demodulation,[],[f65,f179])).
% 1.39/0.56  fof(f179,plain,(
% 1.39/0.56    k1_xboole_0 = sK2 | ~spl8_19),
% 1.39/0.56    inference(avatar_component_clause,[],[f177])).
% 1.39/0.56  fof(f65,plain,(
% 1.39/0.56    m1_subset_1(sK5,k1_zfmisc_1(sK2)) | ~spl8_3),
% 1.39/0.56    inference(avatar_component_clause,[],[f63])).
% 1.39/0.56  fof(f185,plain,(
% 1.39/0.56    k7_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(sK6) | r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k2_mcart_1(sK6),sK5)),
% 1.39/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.39/0.56  fof(f166,plain,(
% 1.39/0.56    ~spl8_16 | ~spl8_15),
% 1.39/0.56    inference(avatar_split_clause,[],[f161,f156,f163])).
% 1.39/0.56  fof(f156,plain,(
% 1.39/0.56    spl8_15 <=> r2_hidden(k2_mcart_1(sK6),sK5)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 1.39/0.56  fof(f161,plain,(
% 1.39/0.56    ~v1_xboole_0(sK5) | ~spl8_15),
% 1.39/0.56    inference(resolution,[],[f158,f31])).
% 1.39/0.56  fof(f158,plain,(
% 1.39/0.56    r2_hidden(k2_mcart_1(sK6),sK5) | ~spl8_15),
% 1.39/0.56    inference(avatar_component_clause,[],[f156])).
% 1.39/0.56  fof(f159,plain,(
% 1.39/0.56    spl8_15 | ~spl8_4),
% 1.39/0.56    inference(avatar_split_clause,[],[f153,f68,f156])).
% 1.39/0.56  fof(f68,plain,(
% 1.39/0.56    spl8_4 <=> r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.39/0.56  fof(f153,plain,(
% 1.39/0.56    r2_hidden(k2_mcart_1(sK6),sK5) | ~spl8_4),
% 1.39/0.56    inference(resolution,[],[f43,f70])).
% 1.39/0.56  fof(f70,plain,(
% 1.39/0.56    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | ~spl8_4),
% 1.39/0.56    inference(avatar_component_clause,[],[f68])).
% 1.39/0.56  fof(f147,plain,(
% 1.39/0.56    spl8_14 | ~spl8_4),
% 1.39/0.56    inference(avatar_split_clause,[],[f141,f68,f144])).
% 1.39/0.56  fof(f141,plain,(
% 1.39/0.56    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) | ~spl8_4),
% 1.39/0.56    inference(resolution,[],[f42,f70])).
% 1.39/0.56  fof(f89,plain,(
% 1.39/0.56    ~spl8_6 | ~spl8_7 | ~spl8_8),
% 1.39/0.56    inference(avatar_split_clause,[],[f24,f86,f82,f78])).
% 1.39/0.56  fof(f78,plain,(
% 1.39/0.56    spl8_6 <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.39/0.56  fof(f82,plain,(
% 1.39/0.56    spl8_7 <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.39/0.56  fof(f86,plain,(
% 1.39/0.56    spl8_8 <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.39/0.56  fof(f24,plain,(
% 1.39/0.56    ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)),
% 1.39/0.56    inference(cnf_transformation,[],[f15])).
% 1.39/0.56  fof(f15,plain,(
% 1.39/0.56    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 1.39/0.56    inference(flattening,[],[f14])).
% 1.39/0.56  fof(f14,plain,(
% 1.39/0.56    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f12])).
% 1.39/0.56  fof(f12,negated_conjecture,(
% 1.39/0.56    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 1.39/0.56    inference(negated_conjecture,[],[f11])).
% 1.39/0.56  fof(f11,conjecture,(
% 1.39/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_mcart_1)).
% 1.39/0.56  fof(f76,plain,(
% 1.39/0.56    spl8_5),
% 1.39/0.56    inference(avatar_split_clause,[],[f48,f73])).
% 1.39/0.56  fof(f48,plain,(
% 1.39/0.56    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.39/0.56    inference(definition_unfolding,[],[f25,f39])).
% 1.39/0.56  fof(f25,plain,(
% 1.39/0.56    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.39/0.56    inference(cnf_transformation,[],[f15])).
% 1.39/0.56  fof(f71,plain,(
% 1.39/0.56    spl8_4),
% 1.39/0.56    inference(avatar_split_clause,[],[f47,f68])).
% 1.39/0.56  fof(f47,plain,(
% 1.39/0.56    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 1.39/0.56    inference(definition_unfolding,[],[f26,f39])).
% 1.39/0.56  fof(f26,plain,(
% 1.39/0.56    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))),
% 1.39/0.56    inference(cnf_transformation,[],[f15])).
% 1.39/0.56  fof(f66,plain,(
% 1.39/0.56    spl8_3),
% 1.39/0.56    inference(avatar_split_clause,[],[f27,f63])).
% 1.39/0.56  fof(f27,plain,(
% 1.39/0.56    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 1.39/0.56    inference(cnf_transformation,[],[f15])).
% 1.39/0.56  fof(f61,plain,(
% 1.39/0.56    spl8_2),
% 1.39/0.56    inference(avatar_split_clause,[],[f28,f58])).
% 1.39/0.56  fof(f28,plain,(
% 1.39/0.56    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 1.39/0.56    inference(cnf_transformation,[],[f15])).
% 1.39/0.56  fof(f56,plain,(
% 1.39/0.56    spl8_1),
% 1.39/0.56    inference(avatar_split_clause,[],[f29,f53])).
% 1.39/0.56  fof(f29,plain,(
% 1.39/0.56    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.39/0.56    inference(cnf_transformation,[],[f15])).
% 1.39/0.56  % SZS output end Proof for theBenchmark
% 1.39/0.56  % (5827)------------------------------
% 1.39/0.56  % (5827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (5827)Termination reason: Refutation
% 1.39/0.56  
% 1.39/0.56  % (5827)Memory used [KB]: 11001
% 1.39/0.56  % (5827)Time elapsed: 0.140 s
% 1.39/0.56  % (5827)------------------------------
% 1.39/0.56  % (5827)------------------------------
% 1.39/0.56  % (5828)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.39/0.56  % (5809)Success in time 0.193 s
%------------------------------------------------------------------------------
