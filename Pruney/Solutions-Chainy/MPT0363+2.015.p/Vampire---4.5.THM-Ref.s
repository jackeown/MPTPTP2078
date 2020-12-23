%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 127 expanded)
%              Number of leaves         :   19 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :  259 ( 462 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f303,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f57,f62,f67,f96,f142,f223,f235,f259,f302])).

fof(f302,plain,
    ( ~ spl5_1
    | ~ spl5_8
    | spl5_17 ),
    inference(avatar_contradiction_clause,[],[f301])).

fof(f301,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_8
    | spl5_17 ),
    inference(subsumption_resolution,[],[f300,f141])).

fof(f141,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl5_8
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f300,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ spl5_1
    | spl5_17 ),
    inference(subsumption_resolution,[],[f292,f50])).

fof(f50,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl5_1
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f292,plain,
    ( ~ r1_xboole_0(sK2,sK3)
    | ~ r1_tarski(sK2,sK1)
    | spl5_17 ),
    inference(resolution,[],[f46,f258])).

fof(f258,plain,
    ( ~ r1_tarski(sK2,k4_xboole_0(sK1,sK3))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl5_17
  <=> r1_tarski(sK2,k4_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f259,plain,
    ( ~ spl5_17
    | spl5_2
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f254,f220,f53,f256])).

fof(f53,plain,
    ( spl5_2
  <=> r1_tarski(sK2,k3_subset_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f220,plain,
    ( spl5_13
  <=> k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f254,plain,
    ( ~ r1_tarski(sK2,k4_xboole_0(sK1,sK3))
    | spl5_2
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f55,f222])).

fof(f222,plain,
    ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f220])).

fof(f55,plain,
    ( ~ r1_tarski(sK2,k3_subset_1(sK1,sK3))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f235,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f233,f61])).

fof(f61,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f233,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f208,f114])).

fof(f114,plain,
    ( ! [X0] : ~ r1_tarski(sK2,k4_xboole_0(X0,sK3))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f51,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f51,plain,
    ( ~ r1_xboole_0(sK2,sK3)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f208,plain,
    ( r1_tarski(sK2,k4_xboole_0(sK1,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | ~ spl5_2 ),
    inference(superposition,[],[f54,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f54,plain,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK3))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f223,plain,
    ( spl5_13
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f201,f59,f220])).

fof(f201,plain,
    ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3)
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f61,f37])).

fof(f142,plain,
    ( spl5_8
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f130,f84,f139])).

fof(f84,plain,
    ( spl5_5
  <=> r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f130,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f86,f47,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ sP0(X0,X1)
      | ~ r2_hidden(X3,X1)
      | r1_tarski(X3,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f47,plain,(
    ! [X0] : sP0(X0,k1_zfmisc_1(X0)) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f3,f15])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f86,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f96,plain,
    ( spl5_5
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f95,f64,f84])).

fof(f64,plain,
    ( spl5_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f95,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f81,f32])).

fof(f32,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f81,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1))
    | ~ spl5_4 ),
    inference(resolution,[],[f33,f66])).

fof(f66,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f67,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f28,f64])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ r1_tarski(sK2,k3_subset_1(sK1,sK3))
      | ~ r1_xboole_0(sK2,sK3) )
    & ( r1_tarski(sK2,k3_subset_1(sK1,sK3))
      | r1_xboole_0(sK2,sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f20,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | r1_xboole_0(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK2,k3_subset_1(sK1,X2))
            | ~ r1_xboole_0(sK2,X2) )
          & ( r1_tarski(sK2,k3_subset_1(sK1,X2))
            | r1_xboole_0(sK2,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(sK2,k3_subset_1(sK1,X2))
          | ~ r1_xboole_0(sK2,X2) )
        & ( r1_tarski(sK2,k3_subset_1(sK1,X2))
          | r1_xboole_0(sK2,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
   => ( ( ~ r1_tarski(sK2,k3_subset_1(sK1,sK3))
        | ~ r1_xboole_0(sK2,sK3) )
      & ( r1_tarski(sK2,k3_subset_1(sK1,sK3))
        | r1_xboole_0(sK2,sK3) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
            | ~ r1_xboole_0(X1,X2) )
          & ( r1_tarski(X1,k3_subset_1(X0,X2))
            | r1_xboole_0(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
            | ~ r1_xboole_0(X1,X2) )
          & ( r1_tarski(X1,k3_subset_1(X0,X2))
            | r1_xboole_0(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,X2)
          <~> r1_tarski(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,X2)
            <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

fof(f62,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f29,f59])).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f30,f53,f49])).

fof(f30,plain,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK3))
    | r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f31,f53,f49])).

fof(f31,plain,
    ( ~ r1_tarski(sK2,k3_subset_1(sK1,sK3))
    | ~ r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:13:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (17291)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.47  % (17289)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (17291)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (17284)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (17281)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f303,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f56,f57,f62,f67,f96,f142,f223,f235,f259,f302])).
% 0.21/0.47  fof(f302,plain,(
% 0.21/0.47    ~spl5_1 | ~spl5_8 | spl5_17),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f301])).
% 0.21/0.47  fof(f301,plain,(
% 0.21/0.47    $false | (~spl5_1 | ~spl5_8 | spl5_17)),
% 0.21/0.47    inference(subsumption_resolution,[],[f300,f141])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    r1_tarski(sK2,sK1) | ~spl5_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f139])).
% 0.21/0.47  fof(f139,plain,(
% 0.21/0.47    spl5_8 <=> r1_tarski(sK2,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.47  fof(f300,plain,(
% 0.21/0.47    ~r1_tarski(sK2,sK1) | (~spl5_1 | spl5_17)),
% 0.21/0.47    inference(subsumption_resolution,[],[f292,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    r1_xboole_0(sK2,sK3) | ~spl5_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    spl5_1 <=> r1_xboole_0(sK2,sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.47  fof(f292,plain,(
% 0.21/0.47    ~r1_xboole_0(sK2,sK3) | ~r1_tarski(sK2,sK1) | spl5_17),
% 0.21/0.47    inference(resolution,[],[f46,f258])).
% 0.21/0.47  fof(f258,plain,(
% 0.21/0.47    ~r1_tarski(sK2,k4_xboole_0(sK1,sK3)) | spl5_17),
% 0.21/0.47    inference(avatar_component_clause,[],[f256])).
% 0.21/0.47  fof(f256,plain,(
% 0.21/0.47    spl5_17 <=> r1_tarski(sK2,k4_xboole_0(sK1,sK3))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.21/0.47  fof(f259,plain,(
% 0.21/0.47    ~spl5_17 | spl5_2 | ~spl5_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f254,f220,f53,f256])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    spl5_2 <=> r1_tarski(sK2,k3_subset_1(sK1,sK3))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.47  fof(f220,plain,(
% 0.21/0.47    spl5_13 <=> k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.47  fof(f254,plain,(
% 0.21/0.47    ~r1_tarski(sK2,k4_xboole_0(sK1,sK3)) | (spl5_2 | ~spl5_13)),
% 0.21/0.47    inference(forward_demodulation,[],[f55,f222])).
% 0.21/0.47  fof(f222,plain,(
% 0.21/0.47    k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) | ~spl5_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f220])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ~r1_tarski(sK2,k3_subset_1(sK1,sK3)) | spl5_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f53])).
% 0.21/0.47  fof(f235,plain,(
% 0.21/0.47    spl5_1 | ~spl5_2 | ~spl5_3),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f234])).
% 0.21/0.47  fof(f234,plain,(
% 0.21/0.47    $false | (spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.21/0.47    inference(subsumption_resolution,[],[f233,f61])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    m1_subset_1(sK3,k1_zfmisc_1(sK1)) | ~spl5_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    spl5_3 <=> m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.47  fof(f233,plain,(
% 0.21/0.47    ~m1_subset_1(sK3,k1_zfmisc_1(sK1)) | (spl5_1 | ~spl5_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f208,f114])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_tarski(sK2,k4_xboole_0(X0,sK3))) ) | spl5_1),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f51,f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ~r1_xboole_0(sK2,sK3) | spl5_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f49])).
% 0.21/0.47  fof(f208,plain,(
% 0.21/0.47    r1_tarski(sK2,k4_xboole_0(sK1,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(sK1)) | ~spl5_2),
% 0.21/0.47    inference(superposition,[],[f54,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    r1_tarski(sK2,k3_subset_1(sK1,sK3)) | ~spl5_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f53])).
% 0.21/0.47  fof(f223,plain,(
% 0.21/0.47    spl5_13 | ~spl5_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f201,f59,f220])).
% 0.21/0.47  fof(f201,plain,(
% 0.21/0.47    k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) | ~spl5_3),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f61,f37])).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    spl5_8 | ~spl5_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f130,f84,f139])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    spl5_5 <=> r2_hidden(sK2,k1_zfmisc_1(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    r1_tarski(sK2,sK1) | ~spl5_5),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f86,f47,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (~sP0(X0,X1) | ~r2_hidden(X3,X1) | r1_tarski(X3,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0,X1] : ((sP0(X0,X1) | ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 0.21/0.47    inference(rectify,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 0.21/0.47    inference(nnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X0] : (sP0(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(equality_resolution,[],[f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0,X1] : (sP0(X0,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.47    inference(nnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> sP0(X0,X1))),
% 0.21/0.47    inference(definition_folding,[],[f3,f15])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    r2_hidden(sK2,k1_zfmisc_1(sK1)) | ~spl5_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f84])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    spl5_5 | ~spl5_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f95,f64,f84])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    spl5_4 <=> m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    r2_hidden(sK2,k1_zfmisc_1(sK1)) | ~spl5_4),
% 0.21/0.47    inference(subsumption_resolution,[],[f81,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) | ~spl5_4),
% 0.21/0.48    inference(resolution,[],[f33,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(sK1)) | ~spl5_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f64])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.48    inference(nnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    spl5_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f64])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ((~r1_tarski(sK2,k3_subset_1(sK1,sK3)) | ~r1_xboole_0(sK2,sK3)) & (r1_tarski(sK2,k3_subset_1(sK1,sK3)) | r1_xboole_0(sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f20,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(sK2,k3_subset_1(sK1,X2)) | ~r1_xboole_0(sK2,X2)) & (r1_tarski(sK2,k3_subset_1(sK1,X2)) | r1_xboole_0(sK2,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ? [X2] : ((~r1_tarski(sK2,k3_subset_1(sK1,X2)) | ~r1_xboole_0(sK2,X2)) & (r1_tarski(sK2,k3_subset_1(sK1,X2)) | r1_xboole_0(sK2,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) => ((~r1_tarski(sK2,k3_subset_1(sK1,sK3)) | ~r1_xboole_0(sK2,sK3)) & (r1_tarski(sK2,k3_subset_1(sK1,sK3)) | r1_xboole_0(sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(sK1)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : (((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(nnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : ((r1_xboole_0(X1,X2) <~> r1_tarski(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f7])).
% 0.21/0.48  fof(f7,conjecture,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    spl5_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f59])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl5_1 | spl5_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f30,f53,f49])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    r1_tarski(sK2,k3_subset_1(sK1,sK3)) | r1_xboole_0(sK2,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ~spl5_1 | ~spl5_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f53,f49])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ~r1_tarski(sK2,k3_subset_1(sK1,sK3)) | ~r1_xboole_0(sK2,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (17291)------------------------------
% 0.21/0.48  % (17291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (17291)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (17291)Memory used [KB]: 10746
% 0.21/0.48  % (17291)Time elapsed: 0.062 s
% 0.21/0.48  % (17291)------------------------------
% 0.21/0.48  % (17291)------------------------------
% 0.21/0.48  % (17274)Success in time 0.118 s
%------------------------------------------------------------------------------
