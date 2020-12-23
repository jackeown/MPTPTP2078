%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 225 expanded)
%              Number of leaves         :   20 (  71 expanded)
%              Depth                    :   11
%              Number of atoms          :  223 ( 707 expanded)
%              Number of equality atoms :   39 (  90 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f393,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f110,f224,f311,f345,f366,f391])).

fof(f391,plain,
    ( ~ spl3_5
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f390])).

fof(f390,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f385,f81])).

fof(f81,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f385,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f362,f184])).

fof(f184,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl3_11
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f362,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(global_subsumption,[],[f116,f144,f282])).

fof(f282,plain,
    ( ~ v1_xboole_0(sK2)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f36,f64])).

fof(f64,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ v1_xboole_0(X2)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f40,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f36,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f31,f30])).

fof(f30,plain,
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

fof(f31,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
        & r1_tarski(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f144,plain,(
    r1_tarski(k8_setfam_1(sK0,sK2),sK0) ),
    inference(resolution,[],[f93,f35])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f93,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
      | r1_tarski(k8_setfam_1(X3,X2),X3) ) ),
    inference(resolution,[],[f46,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f116,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | ~ v1_xboole_0(sK1) ),
    inference(superposition,[],[f37,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X1,X0) = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f53,f39])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f53,plain,(
    ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(subsumption_resolution,[],[f52,f38])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f52,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f37,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f366,plain,
    ( spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f365,f186,f183])).

fof(f186,plain,
    ( spl3_12
  <=> r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f365,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f236,f35])).

fof(f236,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(superposition,[],[f37,f99])).

fof(f99,plain,(
    ! [X2,X3] :
      ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,(
    ! [X2,X3] :
      ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    inference(superposition,[],[f47,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f345,plain,(
    spl3_17 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | spl3_17 ),
    inference(subsumption_resolution,[],[f343,f144])).

fof(f343,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | spl3_17 ),
    inference(forward_demodulation,[],[f326,f53])).

fof(f326,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_17 ),
    inference(backward_demodulation,[],[f37,f323])).

fof(f323,plain,
    ( k1_xboole_0 = sK1
    | spl3_17 ),
    inference(subsumption_resolution,[],[f322,f36])).

fof(f322,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2)
    | spl3_17 ),
    inference(resolution,[],[f310,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f310,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl3_17
  <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f311,plain,
    ( spl3_13
    | ~ spl3_17
    | spl3_12 ),
    inference(avatar_split_clause,[],[f307,f186,f309,f191])).

fof(f191,plain,
    ( spl3_13
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f307,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | k1_xboole_0 = sK1
    | spl3_12 ),
    inference(subsumption_resolution,[],[f305,f34])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f305,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_12 ),
    inference(superposition,[],[f187,f99])).

fof(f187,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f186])).

fof(f224,plain,(
    ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f222,f144])).

fof(f222,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f208,f53])).

fof(f208,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f37,f192])).

fof(f192,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f191])).

fof(f110,plain,(
    ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | ~ spl3_4 ),
    inference(resolution,[],[f84,f42])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f84,plain,
    ( ! [X0,X1] : ~ r1_tarski(k4_xboole_0(X0,X1),X1)
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f83,f78])).

fof(f78,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_4
  <=> ! [X0] : ~ v1_xboole_0(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X1)
      | v1_xboole_0(k4_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f43,f41])).

fof(f41,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f82,plain,
    ( spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f63,f80,f77])).

fof(f63,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f40,f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:01:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.46  % (8624)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.47  % (8616)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.47  % (8620)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (8629)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (8615)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (8616)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (8626)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (8625)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.49  % (8628)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (8614)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (8634)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f393,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f82,f110,f224,f311,f345,f366,f391])).
% 0.22/0.50  fof(f391,plain,(
% 0.22/0.50    ~spl3_5 | ~spl3_11),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f390])).
% 0.22/0.50  fof(f390,plain,(
% 0.22/0.50    $false | (~spl3_5 | ~spl3_11)),
% 0.22/0.50    inference(subsumption_resolution,[],[f385,f81])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0) | ~spl3_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f80])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    spl3_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.50  fof(f385,plain,(
% 0.22/0.50    ~v1_xboole_0(k1_xboole_0) | ~spl3_11),
% 0.22/0.50    inference(backward_demodulation,[],[f362,f184])).
% 0.22/0.50  fof(f184,plain,(
% 0.22/0.50    k1_xboole_0 = sK2 | ~spl3_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f183])).
% 0.22/0.50  fof(f183,plain,(
% 0.22/0.50    spl3_11 <=> k1_xboole_0 = sK2),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.50  fof(f362,plain,(
% 0.22/0.50    ~v1_xboole_0(sK2)),
% 0.22/0.50    inference(global_subsumption,[],[f116,f144,f282])).
% 0.22/0.50  fof(f282,plain,(
% 0.22/0.50    ~v1_xboole_0(sK2) | v1_xboole_0(sK1)),
% 0.22/0.50    inference(resolution,[],[f36,f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X2,X1] : (~r1_tarski(X1,X2) | ~v1_xboole_0(X2) | v1_xboole_0(X1)) )),
% 0.22/0.50    inference(resolution,[],[f40,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.50    inference(nnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    r1_tarski(sK1,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f31,f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(flattening,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.22/0.50    inference(negated_conjecture,[],[f14])).
% 0.22/0.50  fof(f14,conjecture,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    r1_tarski(k8_setfam_1(sK0,sK2),sK0)),
% 0.22/0.50    inference(resolution,[],[f93,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3))) | r1_tarski(k8_setfam_1(X3,X2),X3)) )),
% 0.22/0.50    inference(resolution,[],[f46,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    ~r1_tarski(k8_setfam_1(sK0,sK2),sK0) | ~v1_xboole_0(sK1)),
% 0.22/0.50    inference(superposition,[],[f37,f56])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k8_setfam_1(X1,X0) = X1 | ~v1_xboole_0(X0)) )),
% 0.22/0.50    inference(superposition,[],[f53,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f52,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.50    inference(equality_resolution,[],[f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f366,plain,(
% 0.22/0.50    spl3_11 | ~spl3_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f365,f186,f183])).
% 0.22/0.50  fof(f186,plain,(
% 0.22/0.50    spl3_12 <=> r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.50  fof(f365,plain,(
% 0.22/0.50    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 0.22/0.50    inference(subsumption_resolution,[],[f236,f35])).
% 0.22/0.50  fof(f236,plain,(
% 0.22/0.50    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.50    inference(superposition,[],[f37,f99])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f96])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) )),
% 0.22/0.50    inference(superposition,[],[f47,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f345,plain,(
% 0.22/0.50    spl3_17),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f344])).
% 0.22/0.50  fof(f344,plain,(
% 0.22/0.50    $false | spl3_17),
% 0.22/0.50    inference(subsumption_resolution,[],[f343,f144])).
% 0.22/0.50  fof(f343,plain,(
% 0.22/0.50    ~r1_tarski(k8_setfam_1(sK0,sK2),sK0) | spl3_17),
% 0.22/0.50    inference(forward_demodulation,[],[f326,f53])).
% 0.22/0.50  fof(f326,plain,(
% 0.22/0.50    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | spl3_17),
% 0.22/0.50    inference(backward_demodulation,[],[f37,f323])).
% 0.22/0.50  fof(f323,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | spl3_17),
% 0.22/0.50    inference(subsumption_resolution,[],[f322,f36])).
% 0.22/0.50  fof(f322,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2) | spl3_17),
% 0.22/0.50    inference(resolution,[],[f310,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.22/0.50  fof(f310,plain,(
% 0.22/0.50    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | spl3_17),
% 0.22/0.50    inference(avatar_component_clause,[],[f309])).
% 0.22/0.50  fof(f309,plain,(
% 0.22/0.50    spl3_17 <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.50  fof(f311,plain,(
% 0.22/0.50    spl3_13 | ~spl3_17 | spl3_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f307,f186,f309,f191])).
% 0.22/0.50  fof(f191,plain,(
% 0.22/0.50    spl3_13 <=> k1_xboole_0 = sK1),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.50  fof(f307,plain,(
% 0.22/0.50    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | k1_xboole_0 = sK1 | spl3_12),
% 0.22/0.50    inference(subsumption_resolution,[],[f305,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f305,plain,(
% 0.22/0.50    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_12),
% 0.22/0.50    inference(superposition,[],[f187,f99])).
% 0.22/0.50  fof(f187,plain,(
% 0.22/0.50    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | spl3_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f186])).
% 0.22/0.50  fof(f224,plain,(
% 0.22/0.50    ~spl3_13),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f223])).
% 0.22/0.50  fof(f223,plain,(
% 0.22/0.50    $false | ~spl3_13),
% 0.22/0.50    inference(subsumption_resolution,[],[f222,f144])).
% 0.22/0.50  fof(f222,plain,(
% 0.22/0.50    ~r1_tarski(k8_setfam_1(sK0,sK2),sK0) | ~spl3_13),
% 0.22/0.50    inference(forward_demodulation,[],[f208,f53])).
% 0.22/0.50  fof(f208,plain,(
% 0.22/0.50    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | ~spl3_13),
% 0.22/0.50    inference(backward_demodulation,[],[f37,f192])).
% 0.22/0.50  fof(f192,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | ~spl3_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f191])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    ~spl3_4),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f106])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    $false | ~spl3_4),
% 0.22/0.50    inference(resolution,[],[f84,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X1)) ) | ~spl3_4),
% 0.22/0.50    inference(subsumption_resolution,[],[f83,f78])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(X0)) ) | ~spl3_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f77])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    spl3_4 <=> ! [X0] : ~v1_xboole_0(X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X1) | v1_xboole_0(k4_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(resolution,[],[f43,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.22/0.50    inference(flattening,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    spl3_4 | spl3_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f63,f80,f77])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X0] : (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(X0)) )),
% 0.22/0.50    inference(resolution,[],[f40,f38])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (8616)------------------------------
% 0.22/0.50  % (8616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (8616)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (8616)Memory used [KB]: 10746
% 0.22/0.50  % (8616)Time elapsed: 0.067 s
% 0.22/0.50  % (8616)------------------------------
% 0.22/0.50  % (8616)------------------------------
% 0.22/0.50  % (8619)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (8613)Success in time 0.148 s
%------------------------------------------------------------------------------
