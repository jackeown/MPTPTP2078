%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 262 expanded)
%              Number of leaves         :   27 (  91 expanded)
%              Depth                    :   15
%              Number of atoms          :  305 ( 777 expanded)
%              Number of equality atoms :   65 ( 145 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f285,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f108,f113,f124,f127,f203,f251,f254,f256,f259,f276,f284])).

fof(f284,plain,
    ( ~ spl4_2
    | spl4_14 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | ~ spl4_2
    | spl4_14 ),
    inference(resolution,[],[f279,f222])).

fof(f222,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f34,f79])).

fof(f79,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f27,f26])).

fof(f26,plain,
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

fof(f27,plain,
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

fof(f279,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl4_14 ),
    inference(resolution,[],[f277,f62])).

fof(f62,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(duplicate_literal_removal,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f49,f58])).

fof(f58,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f277,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | spl4_14 ),
    inference(resolution,[],[f275,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f275,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl4_14 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl4_14
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f276,plain,
    ( ~ spl4_5
    | ~ spl4_14
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f271,f86,f77,f273,f101])).

fof(f101,plain,
    ( spl4_5
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f86,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f271,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(superposition,[],[f266,f58])).

fof(f266,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f258,f88])).

fof(f88,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f258,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f37,f79])).

fof(f37,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f259,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f235,f86,f82])).

fof(f82,plain,
    ( spl4_3
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f235,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    inference(resolution,[],[f35,f66])).

fof(f66,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | k1_xboole_0 = X3
      | k1_setfam_1(X3) = k8_setfam_1(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,(
    ! [X2,X3] :
      ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    inference(superposition,[],[f50,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f256,plain,
    ( spl4_6
    | ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | spl4_6
    | ~ spl4_13 ),
    inference(resolution,[],[f250,f233])).

fof(f233,plain,
    ( ~ m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | spl4_6 ),
    inference(resolution,[],[f107,f52])).

fof(f107,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl4_6
  <=> r1_tarski(k1_setfam_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f250,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl4_13
  <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f254,plain,(
    spl4_12 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | spl4_12 ),
    inference(resolution,[],[f246,f35])).

fof(f246,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl4_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f251,plain,
    ( ~ spl4_12
    | spl4_13
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f242,f82,f248,f244])).

fof(f242,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_3 ),
    inference(superposition,[],[f49,f84])).

fof(f84,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f203,plain,
    ( spl4_2
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | spl4_2
    | ~ spl4_4 ),
    inference(trivial_inequality_removal,[],[f201])).

fof(f201,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl4_2
    | ~ spl4_4 ),
    inference(superposition,[],[f78,f187])).

fof(f187,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(resolution,[],[f185,f131])).

fof(f131,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f36,f88])).

fof(f36,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f185,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f182,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f182,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f180])).

fof(f180,plain,(
    ! [X6,X7] :
      ( k1_xboole_0 != X7
      | ~ m1_subset_1(X6,k1_zfmisc_1(X7))
      | k1_xboole_0 = X6 ) ),
    inference(resolution,[],[f174,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f174,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 != X0 ) ),
    inference(resolution,[],[f173,f39])).

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

fof(f173,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f56,f110])).

fof(f110,plain,(
    ! [X0] :
      ( k5_xboole_0(k1_tarski(sK3(X0)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_tarski(sK3(X0)))))) = X0
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f57,f41])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0))))) = X1 ) ),
    inference(definition_unfolding,[],[f46,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) ),
    inference(definition_unfolding,[],[f45,f54])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f44,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f56,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0))))) ),
    inference(definition_unfolding,[],[f42,f55])).

fof(f42,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f78,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f127,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl4_7 ),
    inference(resolution,[],[f123,f36])).

fof(f123,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl4_7
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f124,plain,
    ( ~ spl4_7
    | spl4_2
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f118,f82,f73,f77,f121])).

fof(f73,plain,
    ( spl4_1
  <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f118,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2)
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(resolution,[],[f114,f47])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f13])).

% (13986)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f114,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f91,f75])).

fof(f75,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f91,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f37,f84])).

fof(f113,plain,
    ( ~ spl4_2
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | ~ spl4_2
    | spl4_5 ),
    inference(resolution,[],[f103,f94])).

fof(f94,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f34,f79])).

fof(f103,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f108,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f99,f82,f77,f105,f101])).

fof(f99,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(superposition,[],[f92,f58])).

fof(f92,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f91,f79])).

fof(f80,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f67,f77,f73])).

fof(f67,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    inference(resolution,[],[f66,f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:29:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (13980)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (13980)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (13996)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.51  % (13988)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.51  % (13990)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (13982)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (13978)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (13978)Refutation not found, incomplete strategy% (13978)------------------------------
% 0.20/0.51  % (13978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (13978)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (13978)Memory used [KB]: 10618
% 0.20/0.51  % (13978)Time elapsed: 0.109 s
% 0.20/0.51  % (13978)------------------------------
% 0.20/0.51  % (13978)------------------------------
% 0.20/0.51  % (13990)Refutation not found, incomplete strategy% (13990)------------------------------
% 0.20/0.51  % (13990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (13972)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (13974)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (13977)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (13990)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (13990)Memory used [KB]: 10746
% 0.20/0.52  % (13990)Time elapsed: 0.059 s
% 0.20/0.52  % (13990)------------------------------
% 0.20/0.52  % (13990)------------------------------
% 0.20/0.52  % (13994)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f285,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f80,f108,f113,f124,f127,f203,f251,f254,f256,f259,f276,f284])).
% 0.20/0.52  fof(f284,plain,(
% 0.20/0.52    ~spl4_2 | spl4_14),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f282])).
% 0.20/0.52  fof(f282,plain,(
% 0.20/0.52    $false | (~spl4_2 | spl4_14)),
% 0.20/0.52    inference(resolution,[],[f279,f222])).
% 0.20/0.52  fof(f222,plain,(
% 0.20/0.52    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_2),
% 0.20/0.52    inference(forward_demodulation,[],[f34,f79])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    k1_xboole_0 = sK1 | ~spl4_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f77])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    spl4_2 <=> k1_xboole_0 = sK1),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f27,f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.53    inference(flattening,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.53    inference(ennf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.20/0.53    inference(negated_conjecture,[],[f14])).
% 0.20/0.53  fof(f14,conjecture,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).
% 0.20/0.53  fof(f279,plain,(
% 0.20/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl4_14),
% 0.20/0.53    inference(resolution,[],[f277,f62])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f61])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.53    inference(superposition,[],[f49,f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.53    inference(equality_resolution,[],[f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 0.20/0.53  fof(f277,plain,(
% 0.20/0.53    ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | spl4_14),
% 0.20/0.53    inference(resolution,[],[f275,f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.53    inference(nnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.53  fof(f275,plain,(
% 0.20/0.53    ~r1_tarski(sK0,sK0) | spl4_14),
% 0.20/0.53    inference(avatar_component_clause,[],[f273])).
% 0.20/0.53  fof(f273,plain,(
% 0.20/0.53    spl4_14 <=> r1_tarski(sK0,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.53  fof(f276,plain,(
% 0.20/0.53    ~spl4_5 | ~spl4_14 | ~spl4_2 | ~spl4_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f271,f86,f77,f273,f101])).
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    spl4_5 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.53  fof(f86,plain,(
% 0.20/0.53    spl4_4 <=> k1_xboole_0 = sK2),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.53  fof(f271,plain,(
% 0.20/0.53    ~r1_tarski(sK0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl4_2 | ~spl4_4)),
% 0.20/0.53    inference(superposition,[],[f266,f58])).
% 0.20/0.53  fof(f266,plain,(
% 0.20/0.53    ~r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0)) | (~spl4_2 | ~spl4_4)),
% 0.20/0.53    inference(backward_demodulation,[],[f258,f88])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    k1_xboole_0 = sK2 | ~spl4_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f86])).
% 0.20/0.53  fof(f258,plain,(
% 0.20/0.53    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | ~spl4_2),
% 0.20/0.53    inference(forward_demodulation,[],[f37,f79])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f259,plain,(
% 0.20/0.53    spl4_3 | spl4_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f235,f86,f82])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    spl4_3 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.53  fof(f235,plain,(
% 0.20/0.53    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.20/0.53    inference(resolution,[],[f35,f66])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | k1_xboole_0 = X3 | k1_setfam_1(X3) = k8_setfam_1(X2,X3)) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f63])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) )),
% 0.20/0.53    inference(superposition,[],[f50,f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f256,plain,(
% 0.20/0.53    spl4_6 | ~spl4_13),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f255])).
% 0.20/0.53  fof(f255,plain,(
% 0.20/0.53    $false | (spl4_6 | ~spl4_13)),
% 0.20/0.53    inference(resolution,[],[f250,f233])).
% 0.20/0.53  fof(f233,plain,(
% 0.20/0.53    ~m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | spl4_6),
% 0.20/0.53    inference(resolution,[],[f107,f52])).
% 0.20/0.53  fof(f107,plain,(
% 0.20/0.53    ~r1_tarski(k1_setfam_1(sK2),sK0) | spl4_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f105])).
% 0.20/0.53  fof(f105,plain,(
% 0.20/0.53    spl4_6 <=> r1_tarski(k1_setfam_1(sK2),sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.53  fof(f250,plain,(
% 0.20/0.53    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~spl4_13),
% 0.20/0.53    inference(avatar_component_clause,[],[f248])).
% 0.20/0.53  fof(f248,plain,(
% 0.20/0.53    spl4_13 <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.53  fof(f254,plain,(
% 0.20/0.53    spl4_12),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f252])).
% 0.20/0.53  fof(f252,plain,(
% 0.20/0.53    $false | spl4_12),
% 0.20/0.53    inference(resolution,[],[f246,f35])).
% 0.20/0.53  fof(f246,plain,(
% 0.20/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl4_12),
% 0.20/0.53    inference(avatar_component_clause,[],[f244])).
% 0.20/0.53  fof(f244,plain,(
% 0.20/0.53    spl4_12 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.53  fof(f251,plain,(
% 0.20/0.53    ~spl4_12 | spl4_13 | ~spl4_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f242,f82,f248,f244])).
% 0.20/0.53  fof(f242,plain,(
% 0.20/0.53    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_3),
% 0.20/0.53    inference(superposition,[],[f49,f84])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl4_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f82])).
% 0.20/0.53  fof(f203,plain,(
% 0.20/0.53    spl4_2 | ~spl4_4),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f202])).
% 0.20/0.53  fof(f202,plain,(
% 0.20/0.53    $false | (spl4_2 | ~spl4_4)),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f201])).
% 0.20/0.53  fof(f201,plain,(
% 0.20/0.53    k1_xboole_0 != k1_xboole_0 | (spl4_2 | ~spl4_4)),
% 0.20/0.53    inference(superposition,[],[f78,f187])).
% 0.20/0.53  fof(f187,plain,(
% 0.20/0.53    k1_xboole_0 = sK1 | ~spl4_4),
% 0.20/0.53    inference(resolution,[],[f185,f131])).
% 0.20/0.53  fof(f131,plain,(
% 0.20/0.53    r1_tarski(sK1,k1_xboole_0) | ~spl4_4),
% 0.20/0.53    inference(backward_demodulation,[],[f36,f88])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    r1_tarski(sK1,sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f185,plain,(
% 0.20/0.53    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 0.20/0.53    inference(resolution,[],[f182,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  fof(f182,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(equality_resolution,[],[f180])).
% 0.20/0.53  fof(f180,plain,(
% 0.20/0.53    ( ! [X6,X7] : (k1_xboole_0 != X7 | ~m1_subset_1(X6,k1_zfmisc_1(X7)) | k1_xboole_0 = X6) )),
% 0.20/0.53    inference(resolution,[],[f174,f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.53  fof(f174,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 != X0) )),
% 0.20/0.53    inference(resolution,[],[f173,f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.20/0.53  fof(f173,plain,(
% 0.20/0.53    ( ! [X0] : (v1_xboole_0(X0) | k1_xboole_0 != X0) )),
% 0.20/0.53    inference(superposition,[],[f56,f110])).
% 0.20/0.53  fof(f110,plain,(
% 0.20/0.53    ( ! [X0] : (k5_xboole_0(k1_tarski(sK3(X0)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_tarski(sK3(X0)))))) = X0 | v1_xboole_0(X0)) )),
% 0.20/0.53    inference(resolution,[],[f57,f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.53    inference(rectify,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.53    inference(nnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0))))) = X1) )),
% 0.20/0.53    inference(definition_unfolding,[],[f46,f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f45,f54])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f44,f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0)))))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f42,f55])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    k1_xboole_0 != sK1 | spl4_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f77])).
% 0.20/0.53  fof(f127,plain,(
% 0.20/0.53    spl4_7),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f125])).
% 0.20/0.53  fof(f125,plain,(
% 0.20/0.53    $false | spl4_7),
% 0.20/0.53    inference(resolution,[],[f123,f36])).
% 0.20/0.53  fof(f123,plain,(
% 0.20/0.53    ~r1_tarski(sK1,sK2) | spl4_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f121])).
% 0.20/0.53  fof(f121,plain,(
% 0.20/0.53    spl4_7 <=> r1_tarski(sK1,sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.53  fof(f124,plain,(
% 0.20/0.53    ~spl4_7 | spl4_2 | ~spl4_1 | ~spl4_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f118,f82,f73,f77,f121])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    spl4_1 <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.53  fof(f118,plain,(
% 0.20/0.53    k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2) | (~spl4_1 | ~spl4_3)),
% 0.20/0.53    inference(resolution,[],[f114,f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.53    inference(flattening,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f13])).
% 0.20/0.53  % (13986)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  fof(f13,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | (~spl4_1 | ~spl4_3)),
% 0.20/0.53    inference(backward_demodulation,[],[f91,f75])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl4_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f73])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | ~spl4_3),
% 0.20/0.53    inference(backward_demodulation,[],[f37,f84])).
% 0.20/0.53  fof(f113,plain,(
% 0.20/0.53    ~spl4_2 | spl4_5),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f111])).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    $false | (~spl4_2 | spl4_5)),
% 0.20/0.53    inference(resolution,[],[f103,f94])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_2),
% 0.20/0.53    inference(backward_demodulation,[],[f34,f79])).
% 0.20/0.53  fof(f103,plain,(
% 0.20/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl4_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f101])).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    ~spl4_5 | ~spl4_6 | ~spl4_2 | ~spl4_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f99,f82,f77,f105,f101])).
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    ~r1_tarski(k1_setfam_1(sK2),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl4_2 | ~spl4_3)),
% 0.20/0.53    inference(superposition,[],[f92,f58])).
% 0.20/0.53  fof(f92,plain,(
% 0.20/0.53    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) | (~spl4_2 | ~spl4_3)),
% 0.20/0.53    inference(backward_demodulation,[],[f91,f79])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    spl4_1 | spl4_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f67,f77,f73])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.20/0.53    inference(resolution,[],[f66,f34])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (13980)------------------------------
% 0.20/0.53  % (13980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (13980)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (13980)Memory used [KB]: 6268
% 0.20/0.53  % (13980)Time elapsed: 0.099 s
% 0.20/0.53  % (13980)------------------------------
% 0.20/0.53  % (13980)------------------------------
% 0.20/0.53  % (13963)Success in time 0.17 s
%------------------------------------------------------------------------------
