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
% DateTime   : Thu Dec  3 12:46:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 240 expanded)
%              Number of leaves         :   27 (  85 expanded)
%              Depth                    :   12
%              Number of atoms          :  298 ( 700 expanded)
%              Number of equality atoms :   48 ( 116 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f274,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f74,f139,f166,f170,f181,f184,f209,f218,f228,f229,f256,f270,f273])).

fof(f273,plain,(
    spl3_15 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | spl3_15 ),
    inference(resolution,[],[f269,f35])).

fof(f35,plain,(
    r1_tarski(sK1,sK2) ),
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

fof(f269,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl3_15
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f270,plain,
    ( ~ spl3_15
    | spl3_6
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f264,f141,f132,f136,f267])).

fof(f136,plain,
    ( spl3_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f132,plain,
    ( spl3_5
  <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f141,plain,
    ( spl3_7
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f264,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2)
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(resolution,[],[f259,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f259,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f150,f134])).

fof(f134,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f132])).

fof(f150,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f36,f143])).

fof(f143,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f141])).

fof(f36,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f256,plain,
    ( ~ spl3_1
    | spl3_6
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | ~ spl3_1
    | spl3_6
    | ~ spl3_8 ),
    inference(trivial_inequality_removal,[],[f254])).

fof(f254,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_1
    | spl3_6
    | ~ spl3_8 ),
    inference(superposition,[],[f137,f241])).

fof(f241,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(resolution,[],[f239,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f239,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(resolution,[],[f231,f78])).

fof(f78,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | v1_xboole_0(X0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f75,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f75,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f64,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f64,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_1
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f231,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f35,f147])).

fof(f147,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl3_8
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f137,plain,
    ( k1_xboole_0 != sK1
    | spl3_6 ),
    inference(avatar_component_clause,[],[f136])).

fof(f229,plain,
    ( spl3_7
    | spl3_8 ),
    inference(avatar_split_clause,[],[f223,f145,f141])).

fof(f223,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    inference(resolution,[],[f34,f115])).

fof(f115,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | k1_xboole_0 = X3
      | k1_setfam_1(X3) = k8_setfam_1(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f228,plain,
    ( spl3_10
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | spl3_10
    | ~ spl3_12 ),
    inference(resolution,[],[f180,f167])).

fof(f167,plain,
    ( ~ m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | spl3_10 ),
    inference(resolution,[],[f165,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f165,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl3_10
  <=> r1_tarski(k1_setfam_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f180,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl3_12
  <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f218,plain,(
    spl3_14 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | spl3_14 ),
    inference(resolution,[],[f215,f37])).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f215,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_14 ),
    inference(resolution,[],[f210,f88])).

fof(f88,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f46,f53])).

fof(f53,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f210,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | spl3_14 ),
    inference(resolution,[],[f208,f49])).

fof(f208,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl3_14
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f209,plain,
    ( ~ spl3_9
    | ~ spl3_14
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f204,f145,f136,f206,f159])).

fof(f159,plain,
    ( spl3_9
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f204,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(superposition,[],[f191,f53])).

fof(f191,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0))
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f185,f147])).

fof(f185,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f36,f138])).

fof(f138,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f136])).

fof(f184,plain,(
    spl3_11 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | spl3_11 ),
    inference(resolution,[],[f176,f34])).

fof(f176,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl3_11
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f181,plain,
    ( ~ spl3_11
    | spl3_12
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f172,f141,f178,f174])).

fof(f172,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_7 ),
    inference(superposition,[],[f46,f143])).

fof(f170,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | spl3_9 ),
    inference(resolution,[],[f161,f37])).

fof(f161,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f159])).

fof(f166,plain,
    ( ~ spl3_9
    | ~ spl3_10
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f157,f141,f136,f163,f159])).

fof(f157,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(superposition,[],[f151,f53])).

fof(f151,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f150,f138])).

fof(f139,plain,
    ( spl3_5
    | spl3_6 ),
    inference(avatar_split_clause,[],[f125,f136,f132])).

fof(f125,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    inference(resolution,[],[f115,f33])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f74,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | ~ spl3_2 ),
    inference(resolution,[],[f69,f37])).

fof(f69,plain,
    ( ! [X0,X1] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k5_xboole_0(X0,k4_xboole_0(X1,X0))))
    | ~ spl3_2 ),
    inference(resolution,[],[f67,f49])).

fof(f67,plain,
    ( ! [X0,X1] : ~ r1_tarski(k1_xboole_0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_2
  <=> ! [X1,X0] : ~ r1_tarski(k1_xboole_0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f68,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f59,f66,f62])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f58,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f20])).

% (7011)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] : r1_xboole_0(k1_xboole_0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f40,f52])).

fof(f52,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:31:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.48  % (7035)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.49  % (7019)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (7027)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.49  % (7019)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f274,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f68,f74,f139,f166,f170,f181,f184,f209,f218,f228,f229,f256,f270,f273])).
% 0.20/0.50  fof(f273,plain,(
% 0.20/0.50    spl3_15),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f271])).
% 0.20/0.50  fof(f271,plain,(
% 0.20/0.50    $false | spl3_15),
% 0.20/0.50    inference(resolution,[],[f269,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    r1_tarski(sK1,sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f30,f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.50    inference(flattening,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.50    inference(ennf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.20/0.50    inference(negated_conjecture,[],[f14])).
% 0.20/0.50  fof(f14,conjecture,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).
% 0.20/0.50  fof(f269,plain,(
% 0.20/0.50    ~r1_tarski(sK1,sK2) | spl3_15),
% 0.20/0.50    inference(avatar_component_clause,[],[f267])).
% 0.20/0.50  fof(f267,plain,(
% 0.20/0.50    spl3_15 <=> r1_tarski(sK1,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.50  fof(f270,plain,(
% 0.20/0.50    ~spl3_15 | spl3_6 | ~spl3_5 | ~spl3_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f264,f141,f132,f136,f267])).
% 0.20/0.50  fof(f136,plain,(
% 0.20/0.50    spl3_6 <=> k1_xboole_0 = sK1),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.50  fof(f132,plain,(
% 0.20/0.50    spl3_5 <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    spl3_7 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.50  fof(f264,plain,(
% 0.20/0.50    k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2) | (~spl3_5 | ~spl3_7)),
% 0.20/0.50    inference(resolution,[],[f259,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,axiom,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.20/0.50  fof(f259,plain,(
% 0.20/0.50    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | (~spl3_5 | ~spl3_7)),
% 0.20/0.50    inference(forward_demodulation,[],[f150,f134])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl3_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f132])).
% 0.20/0.50  fof(f150,plain,(
% 0.20/0.50    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | ~spl3_7),
% 0.20/0.50    inference(backward_demodulation,[],[f36,f143])).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl3_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f141])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f256,plain,(
% 0.20/0.50    ~spl3_1 | spl3_6 | ~spl3_8),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f255])).
% 0.20/0.50  fof(f255,plain,(
% 0.20/0.50    $false | (~spl3_1 | spl3_6 | ~spl3_8)),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f254])).
% 0.20/0.50  fof(f254,plain,(
% 0.20/0.50    k1_xboole_0 != k1_xboole_0 | (~spl3_1 | spl3_6 | ~spl3_8)),
% 0.20/0.50    inference(superposition,[],[f137,f241])).
% 0.20/0.50  fof(f241,plain,(
% 0.20/0.50    k1_xboole_0 = sK1 | (~spl3_1 | ~spl3_8)),
% 0.20/0.50    inference(resolution,[],[f239,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.50  fof(f239,plain,(
% 0.20/0.50    v1_xboole_0(sK1) | (~spl3_1 | ~spl3_8)),
% 0.20/0.50    inference(resolution,[],[f231,f78])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)) ) | ~spl3_1),
% 0.20/0.51    inference(resolution,[],[f75,f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.51    inference(nnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) ) | ~spl3_1),
% 0.20/0.51    inference(resolution,[],[f64,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    v1_xboole_0(k1_xboole_0) | ~spl3_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f62])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    spl3_1 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.51  fof(f231,plain,(
% 0.20/0.51    r1_tarski(sK1,k1_xboole_0) | ~spl3_8),
% 0.20/0.51    inference(backward_demodulation,[],[f35,f147])).
% 0.20/0.51  fof(f147,plain,(
% 0.20/0.51    k1_xboole_0 = sK2 | ~spl3_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f145])).
% 0.20/0.51  fof(f145,plain,(
% 0.20/0.51    spl3_8 <=> k1_xboole_0 = sK2),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.51  fof(f137,plain,(
% 0.20/0.51    k1_xboole_0 != sK1 | spl3_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f136])).
% 0.20/0.51  fof(f229,plain,(
% 0.20/0.51    spl3_7 | spl3_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f223,f145,f141])).
% 0.20/0.51  fof(f223,plain,(
% 0.20/0.51    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.20/0.51    inference(resolution,[],[f34,f115])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | k1_xboole_0 = X3 | k1_setfam_1(X3) = k8_setfam_1(X2,X3)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f112])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) )),
% 0.20/0.51    inference(superposition,[],[f47,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f228,plain,(
% 0.20/0.51    spl3_10 | ~spl3_12),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f227])).
% 0.20/0.51  fof(f227,plain,(
% 0.20/0.51    $false | (spl3_10 | ~spl3_12)),
% 0.20/0.51    inference(resolution,[],[f180,f167])).
% 0.20/0.51  fof(f167,plain,(
% 0.20/0.51    ~m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | spl3_10),
% 0.20/0.51    inference(resolution,[],[f165,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f32])).
% 0.20/0.51  fof(f165,plain,(
% 0.20/0.51    ~r1_tarski(k1_setfam_1(sK2),sK0) | spl3_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f163])).
% 0.20/0.51  fof(f163,plain,(
% 0.20/0.51    spl3_10 <=> r1_tarski(k1_setfam_1(sK2),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.51  fof(f180,plain,(
% 0.20/0.51    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~spl3_12),
% 0.20/0.51    inference(avatar_component_clause,[],[f178])).
% 0.20/0.51  fof(f178,plain,(
% 0.20/0.51    spl3_12 <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.51  fof(f218,plain,(
% 0.20/0.51    spl3_14),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f217])).
% 0.20/0.51  fof(f217,plain,(
% 0.20/0.51    $false | spl3_14),
% 0.20/0.51    inference(resolution,[],[f215,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.51  fof(f215,plain,(
% 0.20/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_14),
% 0.20/0.51    inference(resolution,[],[f210,f88])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f87])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.51    inference(superposition,[],[f46,f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.51    inference(equality_resolution,[],[f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 0.20/0.51  fof(f210,plain,(
% 0.20/0.51    ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | spl3_14),
% 0.20/0.51    inference(resolution,[],[f208,f49])).
% 0.20/0.51  fof(f208,plain,(
% 0.20/0.51    ~r1_tarski(sK0,sK0) | spl3_14),
% 0.20/0.51    inference(avatar_component_clause,[],[f206])).
% 0.20/0.51  fof(f206,plain,(
% 0.20/0.51    spl3_14 <=> r1_tarski(sK0,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.51  fof(f209,plain,(
% 0.20/0.51    ~spl3_9 | ~spl3_14 | ~spl3_6 | ~spl3_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f204,f145,f136,f206,f159])).
% 0.20/0.51  fof(f159,plain,(
% 0.20/0.51    spl3_9 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.51  fof(f204,plain,(
% 0.20/0.51    ~r1_tarski(sK0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl3_6 | ~spl3_8)),
% 0.20/0.51    inference(superposition,[],[f191,f53])).
% 0.20/0.51  fof(f191,plain,(
% 0.20/0.51    ~r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0)) | (~spl3_6 | ~spl3_8)),
% 0.20/0.51    inference(backward_demodulation,[],[f185,f147])).
% 0.20/0.51  fof(f185,plain,(
% 0.20/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | ~spl3_6),
% 0.20/0.51    inference(forward_demodulation,[],[f36,f138])).
% 0.20/0.51  fof(f138,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | ~spl3_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f136])).
% 0.20/0.51  fof(f184,plain,(
% 0.20/0.51    spl3_11),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f182])).
% 0.20/0.51  fof(f182,plain,(
% 0.20/0.51    $false | spl3_11),
% 0.20/0.51    inference(resolution,[],[f176,f34])).
% 0.20/0.51  fof(f176,plain,(
% 0.20/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f174])).
% 0.20/0.51  fof(f174,plain,(
% 0.20/0.51    spl3_11 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.51  fof(f181,plain,(
% 0.20/0.51    ~spl3_11 | spl3_12 | ~spl3_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f172,f141,f178,f174])).
% 0.20/0.51  fof(f172,plain,(
% 0.20/0.51    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_7),
% 0.20/0.51    inference(superposition,[],[f46,f143])).
% 0.20/0.51  fof(f170,plain,(
% 0.20/0.51    spl3_9),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f168])).
% 0.20/0.51  fof(f168,plain,(
% 0.20/0.51    $false | spl3_9),
% 0.20/0.51    inference(resolution,[],[f161,f37])).
% 0.20/0.51  fof(f161,plain,(
% 0.20/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f159])).
% 0.20/0.51  fof(f166,plain,(
% 0.20/0.51    ~spl3_9 | ~spl3_10 | ~spl3_6 | ~spl3_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f157,f141,f136,f163,f159])).
% 0.20/0.51  fof(f157,plain,(
% 0.20/0.51    ~r1_tarski(k1_setfam_1(sK2),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl3_6 | ~spl3_7)),
% 0.20/0.51    inference(superposition,[],[f151,f53])).
% 0.20/0.51  fof(f151,plain,(
% 0.20/0.51    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) | (~spl3_6 | ~spl3_7)),
% 0.20/0.51    inference(backward_demodulation,[],[f150,f138])).
% 0.20/0.51  fof(f139,plain,(
% 0.20/0.51    spl3_5 | spl3_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f125,f136,f132])).
% 0.20/0.51  fof(f125,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.20/0.51    inference(resolution,[],[f115,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    ~spl3_2),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f71])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    $false | ~spl3_2),
% 0.20/0.51    inference(resolution,[],[f69,f37])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k5_xboole_0(X0,k4_xboole_0(X1,X0))))) ) | ~spl3_2),
% 0.20/0.51    inference(resolution,[],[f67,f49])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ) | ~spl3_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f66])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    spl3_2 <=> ! [X1,X0] : ~r1_tarski(k1_xboole_0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    spl3_1 | spl3_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f59,f66,f62])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) | v1_xboole_0(k1_xboole_0)) )),
% 0.20/0.51    inference(resolution,[],[f58,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.20/0.51    inference(flattening,[],[f20])).
% 0.20/0.51  % (7011)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_xboole_0(k1_xboole_0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 0.20/0.51    inference(superposition,[],[f40,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f41,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (7019)------------------------------
% 0.20/0.51  % (7019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (7019)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (7019)Memory used [KB]: 6268
% 0.20/0.51  % (7019)Time elapsed: 0.090 s
% 0.20/0.51  % (7019)------------------------------
% 0.20/0.51  % (7019)------------------------------
% 0.20/0.51  % (7006)Success in time 0.156 s
%------------------------------------------------------------------------------
