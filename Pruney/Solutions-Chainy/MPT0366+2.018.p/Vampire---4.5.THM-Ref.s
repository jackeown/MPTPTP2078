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
% DateTime   : Thu Dec  3 12:45:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 151 expanded)
%              Number of leaves         :   25 (  68 expanded)
%              Depth                    :    7
%              Number of atoms          :  272 ( 583 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f362,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f62,f66,f70,f78,f86,f90,f96,f103,f114,f134,f195,f241,f359])).

fof(f359,plain,
    ( spl4_1
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_29
    | ~ spl4_32 ),
    inference(avatar_contradiction_clause,[],[f358])).

fof(f358,plain,
    ( $false
    | spl4_1
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_29
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f357,f36])).

fof(f36,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl4_1
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f357,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK3))
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_29
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f356,f209])).

fof(f209,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK3),k1_zfmisc_1(sK0))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl4_32
  <=> m1_subset_1(k3_subset_1(sK0,sK3),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f356,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK3),k1_zfmisc_1(sK0))
    | r1_tarski(sK1,k3_subset_1(sK0,sK3))
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f353,f113])).

fof(f113,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl4_17
  <=> r1_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f353,plain,
    ( ~ r1_xboole_0(sK1,sK3)
    | ~ m1_subset_1(k3_subset_1(sK0,sK3),k1_zfmisc_1(sK0))
    | r1_tarski(sK1,k3_subset_1(sK0,sK3))
    | ~ spl4_19
    | ~ spl4_29 ),
    inference(superposition,[],[f194,f133])).

fof(f133,plain,
    ( sK3 = k3_subset_1(sK0,k3_subset_1(sK0,sK3))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl4_19
  <=> sK3 = k3_subset_1(sK0,k3_subset_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f194,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(sK1,k3_subset_1(sK0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
        | r1_tarski(sK1,X2) )
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl4_29
  <=> ! [X2] :
        ( ~ r1_xboole_0(sK1,k3_subset_1(sK0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
        | r1_tarski(sK1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f241,plain,
    ( ~ spl4_4
    | ~ spl4_7
    | spl4_32 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_7
    | spl4_32 ),
    inference(subsumption_resolution,[],[f239,f51])).

fof(f51,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl4_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f239,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl4_7
    | spl4_32 ),
    inference(resolution,[],[f210,f65])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f210,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK3),k1_zfmisc_1(sK0))
    | spl4_32 ),
    inference(avatar_component_clause,[],[f208])).

fof(f195,plain,
    ( spl4_29
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f182,f76,f59,f193])).

fof(f59,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f76,plain,
    ( spl4_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X1,X2)
        | ~ r1_xboole_0(X1,k3_subset_1(X0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f182,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(sK1,k3_subset_1(sK0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
        | r1_tarski(sK1,X2) )
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(resolution,[],[f77,f61])).

fof(f61,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f77,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ r1_xboole_0(X1,k3_subset_1(X0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | r1_tarski(X1,X2) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f76])).

fof(f134,plain,
    ( spl4_19
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f126,f68,f49,f131])).

fof(f68,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f126,plain,
    ( sK3 = k3_subset_1(sK0,k3_subset_1(sK0,sK3))
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(resolution,[],[f69,f51])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f68])).

fof(f114,plain,
    ( spl4_17
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f105,f101,f93,f111])).

fof(f93,plain,
    ( spl4_14
  <=> sK3 = k4_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f101,plain,
    ( spl4_15
  <=> ! [X0] : r1_xboole_0(sK1,k4_xboole_0(X0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f105,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(superposition,[],[f102,f95])).

fof(f95,plain,
    ( sK3 = k4_xboole_0(sK3,sK2)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f93])).

fof(f102,plain,
    ( ! [X0] : r1_xboole_0(sK1,k4_xboole_0(X0,sK2))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f101])).

fof(f103,plain,
    ( spl4_15
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f99,f88,f44,f101])).

fof(f44,plain,
    ( spl4_3
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f88,plain,
    ( spl4_13
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f99,plain,
    ( ! [X0] : r1_xboole_0(sK1,k4_xboole_0(X0,sK2))
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(resolution,[],[f89,f46])).

fof(f46,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f89,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_xboole_0(X0,k4_xboole_0(X2,X1)) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f88])).

fof(f96,plain,
    ( spl4_14
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f91,f84,f39,f93])).

fof(f39,plain,
    ( spl4_2
  <=> r1_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f84,plain,
    ( spl4_12
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f91,plain,
    ( sK3 = k4_xboole_0(sK3,sK2)
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(resolution,[],[f85,f41])).

fof(f41,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f84])).

fof(f90,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f32,f88])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f86,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f30,f84])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f78,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f28,f76])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_xboole_0(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

fof(f70,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f27,f68])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f66,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f26,f64])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f62,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f20,f59])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK3))
    & r1_xboole_0(sK3,sK2)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f16,f15,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
                & r1_xboole_0(X3,X2)
                & r1_tarski(X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(sK1,k3_subset_1(sK0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(sK1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(sK1,k3_subset_1(sK0,X3))
            & r1_xboole_0(X3,X2)
            & r1_tarski(sK1,X2)
            & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ? [X3] :
          ( ~ r1_tarski(sK1,k3_subset_1(sK0,X3))
          & r1_xboole_0(X3,sK2)
          & r1_tarski(sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X3] :
        ( ~ r1_tarski(sK1,k3_subset_1(sK0,X3))
        & r1_xboole_0(X3,sK2)
        & r1_tarski(sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK3))
      & r1_xboole_0(sK3,sK2)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( ( r1_xboole_0(X3,X2)
                    & r1_tarski(X1,X2) )
                 => r1_tarski(X1,k3_subset_1(X0,X3)) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X0))
             => ( ( r1_xboole_0(X3,X2)
                  & r1_tarski(X1,X2) )
               => r1_tarski(X1,k3_subset_1(X0,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_subset_1)).

fof(f52,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f22,f49])).

fof(f22,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f23,f44])).

fof(f23,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f24,f39])).

fof(f24,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f25,f34])).

fof(f25,plain,(
    ~ r1_tarski(sK1,k3_subset_1(sK0,sK3)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:37:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (17152)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (17155)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.42  % (17156)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.42  % (17152)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f362,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f62,f66,f70,f78,f86,f90,f96,f103,f114,f134,f195,f241,f359])).
% 0.21/0.42  fof(f359,plain,(
% 0.21/0.42    spl4_1 | ~spl4_17 | ~spl4_19 | ~spl4_29 | ~spl4_32),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f358])).
% 0.21/0.42  fof(f358,plain,(
% 0.21/0.42    $false | (spl4_1 | ~spl4_17 | ~spl4_19 | ~spl4_29 | ~spl4_32)),
% 0.21/0.42    inference(subsumption_resolution,[],[f357,f36])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    ~r1_tarski(sK1,k3_subset_1(sK0,sK3)) | spl4_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f34])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    spl4_1 <=> r1_tarski(sK1,k3_subset_1(sK0,sK3))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.42  fof(f357,plain,(
% 0.21/0.42    r1_tarski(sK1,k3_subset_1(sK0,sK3)) | (~spl4_17 | ~spl4_19 | ~spl4_29 | ~spl4_32)),
% 0.21/0.42    inference(subsumption_resolution,[],[f356,f209])).
% 0.21/0.42  fof(f209,plain,(
% 0.21/0.42    m1_subset_1(k3_subset_1(sK0,sK3),k1_zfmisc_1(sK0)) | ~spl4_32),
% 0.21/0.42    inference(avatar_component_clause,[],[f208])).
% 0.21/0.42  fof(f208,plain,(
% 0.21/0.42    spl4_32 <=> m1_subset_1(k3_subset_1(sK0,sK3),k1_zfmisc_1(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.21/0.42  fof(f356,plain,(
% 0.21/0.42    ~m1_subset_1(k3_subset_1(sK0,sK3),k1_zfmisc_1(sK0)) | r1_tarski(sK1,k3_subset_1(sK0,sK3)) | (~spl4_17 | ~spl4_19 | ~spl4_29)),
% 0.21/0.42    inference(subsumption_resolution,[],[f353,f113])).
% 0.21/0.42  fof(f113,plain,(
% 0.21/0.42    r1_xboole_0(sK1,sK3) | ~spl4_17),
% 0.21/0.42    inference(avatar_component_clause,[],[f111])).
% 0.21/0.42  fof(f111,plain,(
% 0.21/0.42    spl4_17 <=> r1_xboole_0(sK1,sK3)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.42  fof(f353,plain,(
% 0.21/0.42    ~r1_xboole_0(sK1,sK3) | ~m1_subset_1(k3_subset_1(sK0,sK3),k1_zfmisc_1(sK0)) | r1_tarski(sK1,k3_subset_1(sK0,sK3)) | (~spl4_19 | ~spl4_29)),
% 0.21/0.42    inference(superposition,[],[f194,f133])).
% 0.21/0.42  fof(f133,plain,(
% 0.21/0.42    sK3 = k3_subset_1(sK0,k3_subset_1(sK0,sK3)) | ~spl4_19),
% 0.21/0.42    inference(avatar_component_clause,[],[f131])).
% 0.21/0.42  fof(f131,plain,(
% 0.21/0.42    spl4_19 <=> sK3 = k3_subset_1(sK0,k3_subset_1(sK0,sK3))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.42  fof(f194,plain,(
% 0.21/0.42    ( ! [X2] : (~r1_xboole_0(sK1,k3_subset_1(sK0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | r1_tarski(sK1,X2)) ) | ~spl4_29),
% 0.21/0.42    inference(avatar_component_clause,[],[f193])).
% 0.21/0.42  fof(f193,plain,(
% 0.21/0.42    spl4_29 <=> ! [X2] : (~r1_xboole_0(sK1,k3_subset_1(sK0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | r1_tarski(sK1,X2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.21/0.42  fof(f241,plain,(
% 0.21/0.42    ~spl4_4 | ~spl4_7 | spl4_32),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f240])).
% 0.21/0.42  fof(f240,plain,(
% 0.21/0.42    $false | (~spl4_4 | ~spl4_7 | spl4_32)),
% 0.21/0.42    inference(subsumption_resolution,[],[f239,f51])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl4_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f49])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    spl4_4 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.42  fof(f239,plain,(
% 0.21/0.42    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | (~spl4_7 | spl4_32)),
% 0.21/0.42    inference(resolution,[],[f210,f65])).
% 0.21/0.42  fof(f65,plain,(
% 0.21/0.42    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl4_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f64])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    spl4_7 <=> ! [X1,X0] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.42  fof(f210,plain,(
% 0.21/0.42    ~m1_subset_1(k3_subset_1(sK0,sK3),k1_zfmisc_1(sK0)) | spl4_32),
% 0.21/0.42    inference(avatar_component_clause,[],[f208])).
% 0.21/0.42  fof(f195,plain,(
% 0.21/0.42    spl4_29 | ~spl4_6 | ~spl4_10),
% 0.21/0.42    inference(avatar_split_clause,[],[f182,f76,f59,f193])).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    spl4_6 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    spl4_10 <=> ! [X1,X0,X2] : (r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.42  fof(f182,plain,(
% 0.21/0.42    ( ! [X2] : (~r1_xboole_0(sK1,k3_subset_1(sK0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | r1_tarski(sK1,X2)) ) | (~spl4_6 | ~spl4_10)),
% 0.21/0.42    inference(resolution,[],[f77,f61])).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl4_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f59])).
% 0.21/0.42  fof(f77,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r1_tarski(X1,X2)) ) | ~spl4_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f76])).
% 0.21/0.42  fof(f134,plain,(
% 0.21/0.42    spl4_19 | ~spl4_4 | ~spl4_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f126,f68,f49,f131])).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    spl4_8 <=> ! [X1,X0] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.42  fof(f126,plain,(
% 0.21/0.42    sK3 = k3_subset_1(sK0,k3_subset_1(sK0,sK3)) | (~spl4_4 | ~spl4_8)),
% 0.21/0.42    inference(resolution,[],[f69,f51])).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) ) | ~spl4_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f68])).
% 0.21/0.42  fof(f114,plain,(
% 0.21/0.42    spl4_17 | ~spl4_14 | ~spl4_15),
% 0.21/0.42    inference(avatar_split_clause,[],[f105,f101,f93,f111])).
% 0.21/0.42  fof(f93,plain,(
% 0.21/0.42    spl4_14 <=> sK3 = k4_xboole_0(sK3,sK2)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.42  fof(f101,plain,(
% 0.21/0.42    spl4_15 <=> ! [X0] : r1_xboole_0(sK1,k4_xboole_0(X0,sK2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.42  fof(f105,plain,(
% 0.21/0.42    r1_xboole_0(sK1,sK3) | (~spl4_14 | ~spl4_15)),
% 0.21/0.42    inference(superposition,[],[f102,f95])).
% 0.21/0.42  fof(f95,plain,(
% 0.21/0.42    sK3 = k4_xboole_0(sK3,sK2) | ~spl4_14),
% 0.21/0.42    inference(avatar_component_clause,[],[f93])).
% 0.21/0.42  fof(f102,plain,(
% 0.21/0.42    ( ! [X0] : (r1_xboole_0(sK1,k4_xboole_0(X0,sK2))) ) | ~spl4_15),
% 0.21/0.42    inference(avatar_component_clause,[],[f101])).
% 0.21/0.42  fof(f103,plain,(
% 0.21/0.42    spl4_15 | ~spl4_3 | ~spl4_13),
% 0.21/0.42    inference(avatar_split_clause,[],[f99,f88,f44,f101])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    spl4_3 <=> r1_tarski(sK1,sK2)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.42  fof(f88,plain,(
% 0.21/0.42    spl4_13 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.42  fof(f99,plain,(
% 0.21/0.42    ( ! [X0] : (r1_xboole_0(sK1,k4_xboole_0(X0,sK2))) ) | (~spl4_3 | ~spl4_13)),
% 0.21/0.42    inference(resolution,[],[f89,f46])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    r1_tarski(sK1,sK2) | ~spl4_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f44])).
% 0.21/0.42  fof(f89,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1))) ) | ~spl4_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f88])).
% 0.21/0.42  fof(f96,plain,(
% 0.21/0.42    spl4_14 | ~spl4_2 | ~spl4_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f91,f84,f39,f93])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    spl4_2 <=> r1_xboole_0(sK3,sK2)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.42  fof(f84,plain,(
% 0.21/0.42    spl4_12 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    sK3 = k4_xboole_0(sK3,sK2) | (~spl4_2 | ~spl4_12)),
% 0.21/0.42    inference(resolution,[],[f85,f41])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    r1_xboole_0(sK3,sK2) | ~spl4_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f39])).
% 0.21/0.42  fof(f85,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) ) | ~spl4_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f84])).
% 0.21/0.42  fof(f90,plain,(
% 0.21/0.42    spl4_13),
% 0.21/0.42    inference(avatar_split_clause,[],[f32,f88])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.21/0.42  fof(f86,plain,(
% 0.21/0.42    spl4_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f30,f84])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(nnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    spl4_10),
% 0.21/0.42    inference(avatar_split_clause,[],[f28,f76])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(nnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    spl4_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f27,f68])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    spl4_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f26,f64])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    spl4_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f20,f59])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.42    inference(cnf_transformation,[],[f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ((~r1_tarski(sK1,k3_subset_1(sK0,sK3)) & r1_xboole_0(sK3,sK2) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f16,f15,f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(X1,k3_subset_1(X0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (? [X3] : (~r1_tarski(sK1,k3_subset_1(sK0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(sK1,X2) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ? [X2] : (? [X3] : (~r1_tarski(sK1,k3_subset_1(sK0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(sK1,X2) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (? [X3] : (~r1_tarski(sK1,k3_subset_1(sK0,X3)) & r1_xboole_0(X3,sK2) & r1_tarski(sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ? [X3] : (~r1_tarski(sK1,k3_subset_1(sK0,X3)) & r1_xboole_0(X3,sK2) & r1_tarski(sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(sK0))) => (~r1_tarski(sK1,k3_subset_1(sK0,sK3)) & r1_xboole_0(sK3,sK2) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(sK0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(X1,k3_subset_1(X0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(flattening,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(X1,k3_subset_1(X0,X3)) & (r1_xboole_0(X3,X2) & r1_tarski(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ((r1_xboole_0(X3,X2) & r1_tarski(X1,X2)) => r1_tarski(X1,k3_subset_1(X0,X3))))))),
% 0.21/0.43    inference(negated_conjecture,[],[f6])).
% 0.21/0.43  fof(f6,conjecture,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ((r1_xboole_0(X3,X2) & r1_tarski(X1,X2)) => r1_tarski(X1,k3_subset_1(X0,X3))))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_subset_1)).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    spl4_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f22,f49])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    spl4_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f23,f44])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    r1_tarski(sK1,sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    spl4_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f24,f39])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    r1_xboole_0(sK3,sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    ~spl4_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f25,f34])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ~r1_tarski(sK1,k3_subset_1(sK0,sK3))),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (17152)------------------------------
% 0.21/0.43  % (17152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (17152)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (17152)Memory used [KB]: 10746
% 0.21/0.43  % (17152)Time elapsed: 0.011 s
% 0.21/0.43  % (17152)------------------------------
% 0.21/0.43  % (17152)------------------------------
% 0.21/0.43  % (17146)Success in time 0.068 s
%------------------------------------------------------------------------------
