%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:38 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 257 expanded)
%              Number of leaves         :   34 ( 103 expanded)
%              Depth                    :   13
%              Number of atoms          :  342 ( 711 expanded)
%              Number of equality atoms :   52 ( 111 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f545,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f72,f76,f80,f217,f224,f240,f258,f262,f284,f308,f328,f331,f335,f349,f413,f443,f540])).

fof(f540,plain,(
    spl6_28 ),
    inference(avatar_contradiction_clause,[],[f538])).

fof(f538,plain,
    ( $false
    | spl6_28 ),
    inference(resolution,[],[f348,f89])).

fof(f89,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f60,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f348,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0))
    | spl6_28 ),
    inference(avatar_component_clause,[],[f347])).

fof(f347,plain,
    ( spl6_28
  <=> r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f443,plain,
    ( spl6_13
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f439,f411,f222])).

fof(f222,plain,
    ( spl6_13
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f411,plain,
    ( spl6_33
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f439,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_33 ),
    inference(resolution,[],[f438,f47])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f438,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl6_33 ),
    inference(resolution,[],[f412,f104])).

fof(f104,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X4,k1_xboole_0)
      | ~ r2_hidden(X3,X4) ) ),
    inference(forward_demodulation,[],[f99,f97])).

fof(f97,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f96,f47])).

fof(f96,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(global_subsumption,[],[f46,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f93,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f93,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_xboole_0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(k1_xboole_0,X1)) ) ),
    inference(resolution,[],[f91,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f91,plain,(
    ! [X0] :
      ( r1_xboole_0(k1_xboole_0,X0)
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f57,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f99,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,X4)
      | ~ r1_tarski(X4,k3_xboole_0(k1_xboole_0,X5)) ) ),
    inference(resolution,[],[f96,f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f412,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f411])).

fof(f413,plain,
    ( spl6_33
    | ~ spl6_2
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f351,f215,f70,f411])).

fof(f70,plain,
    ( spl6_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f215,plain,
    ( spl6_11
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f351,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_11 ),
    inference(superposition,[],[f71,f216])).

fof(f216,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f215])).

fof(f71,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f349,plain,
    ( ~ spl6_28
    | ~ spl6_11
    | spl6_25 ),
    inference(avatar_split_clause,[],[f345,f333,f215,f347])).

fof(f333,plain,
    ( spl6_25
  <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f345,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0))
    | ~ spl6_11
    | spl6_25 ),
    inference(forward_demodulation,[],[f334,f216])).

fof(f334,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl6_25 ),
    inference(avatar_component_clause,[],[f333])).

fof(f335,plain,
    ( ~ spl6_25
    | spl6_1
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f268,f222,f66,f333])).

fof(f66,plain,
    ( spl6_1
  <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f268,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl6_1
    | ~ spl6_13 ),
    inference(superposition,[],[f67,f223])).

fof(f223,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f222])).

fof(f67,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f331,plain,
    ( ~ spl6_16
    | spl6_24 ),
    inference(avatar_split_clause,[],[f329,f326,f256])).

fof(f256,plain,
    ( spl6_16
  <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f326,plain,
    ( spl6_24
  <=> r1_tarski(k1_setfam_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f329,plain,
    ( ~ m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | spl6_24 ),
    inference(resolution,[],[f327,f61])).

fof(f327,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | spl6_24 ),
    inference(avatar_component_clause,[],[f326])).

fof(f328,plain,
    ( ~ spl6_23
    | ~ spl6_24
    | spl6_20 ),
    inference(avatar_split_clause,[],[f324,f282,f326,f305])).

fof(f305,plain,
    ( spl6_23
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f282,plain,
    ( spl6_20
  <=> r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f324,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl6_20 ),
    inference(superposition,[],[f283,f64])).

fof(f64,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f283,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl6_20 ),
    inference(avatar_component_clause,[],[f282])).

fof(f308,plain,
    ( k1_xboole_0 != sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f284,plain,
    ( ~ spl6_20
    | spl6_1
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f280,f222,f212,f66,f282])).

fof(f212,plain,
    ( spl6_10
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f280,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl6_1
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f268,f213])).

fof(f213,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f212])).

fof(f262,plain,
    ( ~ spl6_2
    | spl6_13
    | spl6_14 ),
    inference(avatar_split_clause,[],[f259,f238,f222,f70])).

fof(f238,plain,
    ( spl6_14
  <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f259,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2)
    | spl6_14 ),
    inference(resolution,[],[f239,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f239,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl6_14 ),
    inference(avatar_component_clause,[],[f238])).

fof(f258,plain,
    ( ~ spl6_3
    | spl6_16
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f235,f212,f256,f74])).

fof(f74,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f235,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl6_10 ),
    inference(superposition,[],[f53,f213])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

% (11986)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f240,plain,
    ( ~ spl6_14
    | spl6_1
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f236,f219,f212,f66,f238])).

fof(f219,plain,
    ( spl6_12
  <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f236,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl6_1
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f225,f220])).

fof(f220,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f219])).

fof(f225,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | spl6_1
    | ~ spl6_10 ),
    inference(superposition,[],[f67,f213])).

fof(f224,plain,
    ( spl6_12
    | spl6_13
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f205,f78,f222,f219])).

fof(f78,plain,
    ( spl6_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f205,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl6_4 ),
    inference(resolution,[],[f169,f79])).

% (11985)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f79,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f169,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | k1_xboole_0 = X3
      | k1_setfam_1(X3) = k8_setfam_1(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,(
    ! [X2,X3] :
      ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    inference(superposition,[],[f54,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f217,plain,
    ( spl6_10
    | spl6_11
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f204,f74,f215,f212])).

fof(f204,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl6_3 ),
    inference(resolution,[],[f169,f75])).

fof(f75,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f80,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f42,f78])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f30,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
          & r1_tarski(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
        & r1_tarski(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f76,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f43,f74])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f72,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f44,f70])).

fof(f44,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f45,f66])).

fof(f45,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (11973)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (11964)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (11972)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (11983)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (11973)Refutation not found, incomplete strategy% (11973)------------------------------
% 0.20/0.52  % (11973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (11973)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (11973)Memory used [KB]: 10618
% 0.20/0.52  % (11973)Time elapsed: 0.104 s
% 0.20/0.52  % (11973)------------------------------
% 0.20/0.52  % (11973)------------------------------
% 0.20/0.52  % (11964)Refutation not found, incomplete strategy% (11964)------------------------------
% 0.20/0.52  % (11964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (11964)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (11964)Memory used [KB]: 1663
% 0.20/0.52  % (11964)Time elapsed: 0.084 s
% 0.20/0.52  % (11964)------------------------------
% 0.20/0.52  % (11964)------------------------------
% 0.20/0.52  % (11965)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (11988)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % (11967)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (11971)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (11969)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (11975)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (11968)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (11966)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (11987)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.35/0.54  % (11984)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.35/0.54  % (11979)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.35/0.54  % (11983)Refutation found. Thanks to Tanya!
% 1.35/0.54  % SZS status Theorem for theBenchmark
% 1.35/0.54  % SZS output start Proof for theBenchmark
% 1.35/0.54  fof(f545,plain,(
% 1.35/0.54    $false),
% 1.35/0.54    inference(avatar_sat_refutation,[],[f68,f72,f76,f80,f217,f224,f240,f258,f262,f284,f308,f328,f331,f335,f349,f413,f443,f540])).
% 1.35/0.54  fof(f540,plain,(
% 1.35/0.54    spl6_28),
% 1.35/0.54    inference(avatar_contradiction_clause,[],[f538])).
% 1.35/0.54  fof(f538,plain,(
% 1.35/0.54    $false | spl6_28),
% 1.35/0.54    inference(resolution,[],[f348,f89])).
% 1.35/0.54  fof(f89,plain,(
% 1.35/0.54    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.35/0.54    inference(duplicate_literal_removal,[],[f88])).
% 1.35/0.54  fof(f88,plain,(
% 1.35/0.54    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.35/0.54    inference(resolution,[],[f60,f59])).
% 1.35/0.54  fof(f59,plain,(
% 1.35/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f40])).
% 1.35/0.54  fof(f40,plain,(
% 1.35/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.35/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).
% 1.35/0.54  fof(f39,plain,(
% 1.35/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.35/0.54    introduced(choice_axiom,[])).
% 1.35/0.54  fof(f38,plain,(
% 1.35/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.35/0.54    inference(rectify,[],[f37])).
% 1.35/0.54  fof(f37,plain,(
% 1.35/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.35/0.54    inference(nnf_transformation,[],[f26])).
% 1.35/0.54  fof(f26,plain,(
% 1.35/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.35/0.54    inference(ennf_transformation,[],[f1])).
% 1.35/0.54  fof(f1,axiom,(
% 1.35/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.35/0.54  fof(f60,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f40])).
% 1.35/0.54  fof(f348,plain,(
% 1.35/0.54    ~r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0)) | spl6_28),
% 1.35/0.54    inference(avatar_component_clause,[],[f347])).
% 1.35/0.54  fof(f347,plain,(
% 1.35/0.54    spl6_28 <=> r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0))),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 1.35/0.54  fof(f443,plain,(
% 1.35/0.54    spl6_13 | ~spl6_33),
% 1.35/0.54    inference(avatar_split_clause,[],[f439,f411,f222])).
% 1.35/0.54  fof(f222,plain,(
% 1.35/0.54    spl6_13 <=> k1_xboole_0 = sK1),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.35/0.54  fof(f411,plain,(
% 1.35/0.54    spl6_33 <=> r1_tarski(sK1,k1_xboole_0)),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 1.35/0.54  fof(f439,plain,(
% 1.35/0.54    k1_xboole_0 = sK1 | ~spl6_33),
% 1.35/0.54    inference(resolution,[],[f438,f47])).
% 1.35/0.54  fof(f47,plain,(
% 1.35/0.54    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.35/0.54    inference(cnf_transformation,[],[f33])).
% 1.35/0.54  fof(f33,plain,(
% 1.35/0.54    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.35/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f32])).
% 1.35/0.54  fof(f32,plain,(
% 1.35/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.35/0.54    introduced(choice_axiom,[])).
% 1.35/0.54  fof(f18,plain,(
% 1.35/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.35/0.54    inference(ennf_transformation,[],[f4])).
% 1.35/0.54  fof(f4,axiom,(
% 1.35/0.54    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.35/0.54  fof(f438,plain,(
% 1.35/0.54    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | ~spl6_33),
% 1.35/0.54    inference(resolution,[],[f412,f104])).
% 1.35/0.54  fof(f104,plain,(
% 1.35/0.54    ( ! [X4,X3] : (~r1_tarski(X4,k1_xboole_0) | ~r2_hidden(X3,X4)) )),
% 1.35/0.54    inference(forward_demodulation,[],[f99,f97])).
% 1.35/0.54  fof(f97,plain,(
% 1.35/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.35/0.54    inference(resolution,[],[f96,f47])).
% 1.35/0.54  fof(f96,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1))) )),
% 1.35/0.54    inference(global_subsumption,[],[f46,f94])).
% 1.35/0.54  fof(f94,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))) )),
% 1.35/0.54    inference(resolution,[],[f93,f61])).
% 1.35/0.54  fof(f61,plain,(
% 1.35/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f41])).
% 1.35/0.54  fof(f41,plain,(
% 1.35/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.35/0.54    inference(nnf_transformation,[],[f10])).
% 1.35/0.54  fof(f10,axiom,(
% 1.35/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.35/0.54  fof(f93,plain,(
% 1.35/0.54    ( ! [X2,X1] : (~r1_tarski(k1_xboole_0,X1) | ~r2_hidden(X2,k3_xboole_0(k1_xboole_0,X1))) )),
% 1.35/0.54    inference(resolution,[],[f91,f49])).
% 1.35/0.54  fof(f49,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f35])).
% 1.35/0.54  fof(f35,plain,(
% 1.35/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.35/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f34])).
% 1.35/0.54  fof(f34,plain,(
% 1.35/0.54    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.35/0.54    introduced(choice_axiom,[])).
% 1.35/0.54  fof(f19,plain,(
% 1.35/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.35/0.54    inference(ennf_transformation,[],[f15])).
% 1.35/0.54  fof(f15,plain,(
% 1.35/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.35/0.54    inference(rectify,[],[f3])).
% 1.35/0.54  fof(f3,axiom,(
% 1.35/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.35/0.54  fof(f91,plain,(
% 1.35/0.54    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0) | ~r1_tarski(k1_xboole_0,X0)) )),
% 1.35/0.54    inference(equality_resolution,[],[f87])).
% 1.35/0.54  fof(f87,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.35/0.54    inference(superposition,[],[f57,f50])).
% 1.35/0.54  fof(f50,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f20])).
% 1.35/0.54  fof(f20,plain,(
% 1.35/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.35/0.54    inference(ennf_transformation,[],[f5])).
% 1.35/0.54  fof(f5,axiom,(
% 1.35/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.35/0.54  fof(f57,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f36])).
% 1.35/0.54  fof(f36,plain,(
% 1.35/0.54    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.35/0.54    inference(nnf_transformation,[],[f2])).
% 1.35/0.54  fof(f2,axiom,(
% 1.35/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.35/0.54  fof(f46,plain,(
% 1.35/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f6])).
% 1.35/0.54  fof(f6,axiom,(
% 1.35/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.35/0.54  fof(f99,plain,(
% 1.35/0.54    ( ! [X4,X5,X3] : (~r2_hidden(X3,X4) | ~r1_tarski(X4,k3_xboole_0(k1_xboole_0,X5))) )),
% 1.35/0.54    inference(resolution,[],[f96,f58])).
% 1.35/0.54  fof(f58,plain,(
% 1.35/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f40])).
% 1.35/0.54  fof(f412,plain,(
% 1.35/0.54    r1_tarski(sK1,k1_xboole_0) | ~spl6_33),
% 1.35/0.54    inference(avatar_component_clause,[],[f411])).
% 1.35/0.54  fof(f413,plain,(
% 1.35/0.54    spl6_33 | ~spl6_2 | ~spl6_11),
% 1.35/0.54    inference(avatar_split_clause,[],[f351,f215,f70,f411])).
% 1.35/0.54  fof(f70,plain,(
% 1.35/0.54    spl6_2 <=> r1_tarski(sK1,sK2)),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.35/0.54  fof(f215,plain,(
% 1.35/0.54    spl6_11 <=> k1_xboole_0 = sK2),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.35/0.54  fof(f351,plain,(
% 1.35/0.54    r1_tarski(sK1,k1_xboole_0) | (~spl6_2 | ~spl6_11)),
% 1.35/0.54    inference(superposition,[],[f71,f216])).
% 1.35/0.54  fof(f216,plain,(
% 1.35/0.54    k1_xboole_0 = sK2 | ~spl6_11),
% 1.35/0.54    inference(avatar_component_clause,[],[f215])).
% 1.35/0.54  fof(f71,plain,(
% 1.35/0.54    r1_tarski(sK1,sK2) | ~spl6_2),
% 1.35/0.54    inference(avatar_component_clause,[],[f70])).
% 1.35/0.54  fof(f349,plain,(
% 1.35/0.54    ~spl6_28 | ~spl6_11 | spl6_25),
% 1.35/0.54    inference(avatar_split_clause,[],[f345,f333,f215,f347])).
% 1.35/0.54  fof(f333,plain,(
% 1.35/0.54    spl6_25 <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 1.35/0.54  fof(f345,plain,(
% 1.35/0.54    ~r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0)) | (~spl6_11 | spl6_25)),
% 1.35/0.54    inference(forward_demodulation,[],[f334,f216])).
% 1.35/0.54  fof(f334,plain,(
% 1.35/0.54    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | spl6_25),
% 1.35/0.54    inference(avatar_component_clause,[],[f333])).
% 1.35/0.54  fof(f335,plain,(
% 1.35/0.54    ~spl6_25 | spl6_1 | ~spl6_13),
% 1.35/0.54    inference(avatar_split_clause,[],[f268,f222,f66,f333])).
% 1.35/0.54  fof(f66,plain,(
% 1.35/0.54    spl6_1 <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.35/0.54  fof(f268,plain,(
% 1.35/0.54    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | (spl6_1 | ~spl6_13)),
% 1.35/0.54    inference(superposition,[],[f67,f223])).
% 1.35/0.54  fof(f223,plain,(
% 1.35/0.54    k1_xboole_0 = sK1 | ~spl6_13),
% 1.35/0.54    inference(avatar_component_clause,[],[f222])).
% 1.35/0.54  fof(f67,plain,(
% 1.35/0.54    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) | spl6_1),
% 1.35/0.54    inference(avatar_component_clause,[],[f66])).
% 1.35/0.54  fof(f331,plain,(
% 1.35/0.54    ~spl6_16 | spl6_24),
% 1.35/0.54    inference(avatar_split_clause,[],[f329,f326,f256])).
% 1.35/0.54  fof(f256,plain,(
% 1.35/0.54    spl6_16 <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.35/0.54  fof(f326,plain,(
% 1.35/0.54    spl6_24 <=> r1_tarski(k1_setfam_1(sK2),sK0)),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.35/0.54  fof(f329,plain,(
% 1.35/0.54    ~m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | spl6_24),
% 1.35/0.54    inference(resolution,[],[f327,f61])).
% 1.35/0.54  fof(f327,plain,(
% 1.35/0.54    ~r1_tarski(k1_setfam_1(sK2),sK0) | spl6_24),
% 1.35/0.54    inference(avatar_component_clause,[],[f326])).
% 1.35/0.54  fof(f328,plain,(
% 1.35/0.54    ~spl6_23 | ~spl6_24 | spl6_20),
% 1.35/0.54    inference(avatar_split_clause,[],[f324,f282,f326,f305])).
% 1.35/0.54  fof(f305,plain,(
% 1.35/0.54    spl6_23 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.35/0.54  fof(f282,plain,(
% 1.35/0.54    spl6_20 <=> r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 1.35/0.54  fof(f324,plain,(
% 1.35/0.54    ~r1_tarski(k1_setfam_1(sK2),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl6_20),
% 1.35/0.54    inference(superposition,[],[f283,f64])).
% 1.35/0.54  fof(f64,plain,(
% 1.35/0.54    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.35/0.54    inference(equality_resolution,[],[f55])).
% 1.35/0.54  fof(f55,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f25])).
% 1.35/0.54  fof(f25,plain,(
% 1.35/0.54    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.35/0.54    inference(ennf_transformation,[],[f7])).
% 1.35/0.55  fof(f7,axiom,(
% 1.35/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).
% 1.35/0.55  fof(f283,plain,(
% 1.35/0.55    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) | spl6_20),
% 1.35/0.55    inference(avatar_component_clause,[],[f282])).
% 1.35/0.55  fof(f308,plain,(
% 1.35/0.55    k1_xboole_0 != sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.35/0.55    introduced(theory_tautology_sat_conflict,[])).
% 1.35/0.55  fof(f284,plain,(
% 1.35/0.55    ~spl6_20 | spl6_1 | ~spl6_10 | ~spl6_13),
% 1.35/0.55    inference(avatar_split_clause,[],[f280,f222,f212,f66,f282])).
% 1.35/0.55  fof(f212,plain,(
% 1.35/0.55    spl6_10 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.35/0.55  fof(f280,plain,(
% 1.35/0.55    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) | (spl6_1 | ~spl6_10 | ~spl6_13)),
% 1.35/0.55    inference(forward_demodulation,[],[f268,f213])).
% 1.35/0.55  fof(f213,plain,(
% 1.35/0.55    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl6_10),
% 1.35/0.55    inference(avatar_component_clause,[],[f212])).
% 1.35/0.55  fof(f262,plain,(
% 1.35/0.55    ~spl6_2 | spl6_13 | spl6_14),
% 1.35/0.55    inference(avatar_split_clause,[],[f259,f238,f222,f70])).
% 1.35/0.55  fof(f238,plain,(
% 1.35/0.55    spl6_14 <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.35/0.55  fof(f259,plain,(
% 1.35/0.55    k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2) | spl6_14),
% 1.35/0.55    inference(resolution,[],[f239,f51])).
% 1.35/0.55  fof(f51,plain,(
% 1.35/0.55    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f22])).
% 1.35/0.55  fof(f22,plain,(
% 1.35/0.55    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 1.35/0.55    inference(flattening,[],[f21])).
% 1.35/0.55  fof(f21,plain,(
% 1.35/0.55    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 1.35/0.55    inference(ennf_transformation,[],[f12])).
% 1.35/0.55  fof(f12,axiom,(
% 1.35/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).
% 1.35/0.55  fof(f239,plain,(
% 1.35/0.55    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | spl6_14),
% 1.35/0.55    inference(avatar_component_clause,[],[f238])).
% 1.35/0.55  fof(f258,plain,(
% 1.35/0.55    ~spl6_3 | spl6_16 | ~spl6_10),
% 1.35/0.55    inference(avatar_split_clause,[],[f235,f212,f256,f74])).
% 1.35/0.55  fof(f74,plain,(
% 1.35/0.55    spl6_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.35/0.55  fof(f235,plain,(
% 1.35/0.55    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl6_10),
% 1.35/0.55    inference(superposition,[],[f53,f213])).
% 1.35/0.55  fof(f53,plain,(
% 1.35/0.55    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f24])).
% 1.35/0.55  % (11986)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.35/0.55  fof(f24,plain,(
% 1.35/0.55    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.35/0.55    inference(ennf_transformation,[],[f8])).
% 1.35/0.55  fof(f8,axiom,(
% 1.35/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 1.35/0.55  fof(f240,plain,(
% 1.35/0.55    ~spl6_14 | spl6_1 | ~spl6_10 | ~spl6_12),
% 1.35/0.55    inference(avatar_split_clause,[],[f236,f219,f212,f66,f238])).
% 1.35/0.55  fof(f219,plain,(
% 1.35/0.55    spl6_12 <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.35/0.55  fof(f236,plain,(
% 1.35/0.55    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | (spl6_1 | ~spl6_10 | ~spl6_12)),
% 1.35/0.55    inference(forward_demodulation,[],[f225,f220])).
% 1.35/0.55  fof(f220,plain,(
% 1.35/0.55    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl6_12),
% 1.35/0.55    inference(avatar_component_clause,[],[f219])).
% 1.35/0.55  fof(f225,plain,(
% 1.35/0.55    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | (spl6_1 | ~spl6_10)),
% 1.35/0.55    inference(superposition,[],[f67,f213])).
% 1.35/0.55  fof(f224,plain,(
% 1.35/0.55    spl6_12 | spl6_13 | ~spl6_4),
% 1.35/0.55    inference(avatar_split_clause,[],[f205,f78,f222,f219])).
% 1.35/0.55  fof(f78,plain,(
% 1.35/0.55    spl6_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.35/0.55  fof(f205,plain,(
% 1.35/0.55    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl6_4),
% 1.35/0.55    inference(resolution,[],[f169,f79])).
% 1.35/0.55  % (11985)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.35/0.55  fof(f79,plain,(
% 1.35/0.55    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl6_4),
% 1.35/0.55    inference(avatar_component_clause,[],[f78])).
% 1.35/0.55  fof(f169,plain,(
% 1.35/0.55    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | k1_xboole_0 = X3 | k1_setfam_1(X3) = k8_setfam_1(X2,X3)) )),
% 1.35/0.55    inference(duplicate_literal_removal,[],[f166])).
% 1.35/0.55  fof(f166,plain,(
% 1.35/0.55    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) )),
% 1.35/0.55    inference(superposition,[],[f54,f52])).
% 1.35/0.55  fof(f52,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f23])).
% 1.35/0.55  fof(f23,plain,(
% 1.35/0.55    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.35/0.55    inference(ennf_transformation,[],[f9])).
% 1.35/0.55  fof(f9,axiom,(
% 1.35/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 1.35/0.55  fof(f54,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f25])).
% 1.35/0.55  fof(f217,plain,(
% 1.35/0.55    spl6_10 | spl6_11 | ~spl6_3),
% 1.35/0.55    inference(avatar_split_clause,[],[f204,f74,f215,f212])).
% 1.35/0.55  fof(f204,plain,(
% 1.35/0.55    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl6_3),
% 1.35/0.55    inference(resolution,[],[f169,f75])).
% 1.35/0.55  fof(f75,plain,(
% 1.35/0.55    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl6_3),
% 1.35/0.55    inference(avatar_component_clause,[],[f74])).
% 1.35/0.55  fof(f80,plain,(
% 1.35/0.55    spl6_4),
% 1.35/0.55    inference(avatar_split_clause,[],[f42,f78])).
% 1.35/0.55  fof(f42,plain,(
% 1.35/0.55    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.35/0.55    inference(cnf_transformation,[],[f31])).
% 1.35/0.55  fof(f31,plain,(
% 1.35/0.55    (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.35/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f30,f29])).
% 1.35/0.55  fof(f29,plain,(
% 1.35/0.55    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 1.35/0.55    introduced(choice_axiom,[])).
% 1.35/0.55  fof(f30,plain,(
% 1.35/0.55    ? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 1.35/0.55    introduced(choice_axiom,[])).
% 1.35/0.55  fof(f17,plain,(
% 1.35/0.55    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.35/0.55    inference(flattening,[],[f16])).
% 1.35/0.55  fof(f16,plain,(
% 1.35/0.55    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.35/0.55    inference(ennf_transformation,[],[f14])).
% 1.35/0.55  fof(f14,negated_conjecture,(
% 1.35/0.55    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 1.35/0.55    inference(negated_conjecture,[],[f13])).
% 1.35/0.55  fof(f13,conjecture,(
% 1.35/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).
% 1.35/0.55  fof(f76,plain,(
% 1.35/0.55    spl6_3),
% 1.35/0.55    inference(avatar_split_clause,[],[f43,f74])).
% 1.35/0.55  fof(f43,plain,(
% 1.35/0.55    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.35/0.55    inference(cnf_transformation,[],[f31])).
% 1.35/0.55  fof(f72,plain,(
% 1.35/0.55    spl6_2),
% 1.35/0.55    inference(avatar_split_clause,[],[f44,f70])).
% 1.35/0.55  fof(f44,plain,(
% 1.35/0.55    r1_tarski(sK1,sK2)),
% 1.35/0.55    inference(cnf_transformation,[],[f31])).
% 1.35/0.55  fof(f68,plain,(
% 1.35/0.55    ~spl6_1),
% 1.35/0.55    inference(avatar_split_clause,[],[f45,f66])).
% 1.35/0.55  fof(f45,plain,(
% 1.35/0.55    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 1.35/0.55    inference(cnf_transformation,[],[f31])).
% 1.35/0.55  % SZS output end Proof for theBenchmark
% 1.35/0.55  % (11983)------------------------------
% 1.35/0.55  % (11983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (11983)Termination reason: Refutation
% 1.35/0.55  
% 1.35/0.55  % (11983)Memory used [KB]: 11129
% 1.35/0.55  % (11983)Time elapsed: 0.139 s
% 1.35/0.55  % (11983)------------------------------
% 1.35/0.55  % (11983)------------------------------
% 1.35/0.55  % (11963)Success in time 0.189 s
%------------------------------------------------------------------------------
