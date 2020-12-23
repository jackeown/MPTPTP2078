%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 286 expanded)
%              Number of leaves         :   22 (  96 expanded)
%              Depth                    :   13
%              Number of atoms          :  265 ( 726 expanded)
%              Number of equality atoms :   95 ( 285 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f186,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f135,f149,f169,f172,f174,f176,f185])).

fof(f185,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | ~ spl3_2 ),
    inference(trivial_inequality_removal,[],[f183])).

fof(f183,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_2 ),
    inference(resolution,[],[f177,f84])).

fof(f84,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k1_xboole_0 != X0 ) ),
    inference(resolution,[],[f79,f83])).

fof(f83,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f81,f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f81,plain,(
    ! [X2] : r1_xboole_0(X2,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f80])).

fof(f80,plain,(
    ! [X2] :
      ( X2 != X2
      | r1_xboole_0(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f47,f77])).

fof(f77,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f73,f55])).

fof(f55,plain,(
    ! [X0] : k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f51,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f51,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f36,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f36,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f73,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k3_tarski(k2_tarski(k1_xboole_0,X2)) ),
    inference(superposition,[],[f52,f55])).

fof(f52,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f43,f42,f42])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f79,plain,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 != X1 ) ),
    inference(superposition,[],[f48,f77])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f177,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f31,f69])).

fof(f69,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f31,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK0 != sK1
    & r1_tarski(sK0,sK1)
    & v1_zfmisc_1(sK1)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r1_tarski(X0,X1)
            & v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & r1_tarski(sK0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( sK0 != X1
        & r1_tarski(sK0,X1)
        & v1_zfmisc_1(X1)
        & ~ v1_xboole_0(X1) )
   => ( sK0 != sK1
      & r1_tarski(sK0,sK1)
      & v1_zfmisc_1(sK1)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f176,plain,
    ( spl3_5
    | spl3_6
    | spl3_2
    | spl3_7 ),
    inference(avatar_split_clause,[],[f159,f120,f68,f116,f112])).

fof(f112,plain,
    ( spl3_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f116,plain,
    ( spl3_6
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f120,plain,
    ( spl3_7
  <=> ! [X7] : sK1 != k2_tarski(X7,X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f159,plain,(
    ! [X0] :
      ( k2_tarski(X0,X0) != sK1
      | k1_xboole_0 = sK0
      | sK0 = sK1
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f54,f76])).

fof(f76,plain,(
    sK1 = k3_tarski(k2_tarski(sK0,sK1)) ),
    inference(forward_demodulation,[],[f75,f41])).

fof(f75,plain,(
    sK1 = k3_tarski(k2_tarski(sK1,sK0)) ),
    inference(forward_demodulation,[],[f72,f51])).

fof(f72,plain,(
    k3_tarski(k2_tarski(sK1,sK0)) = k3_tarski(k2_tarski(sK1,k1_xboole_0)) ),
    inference(superposition,[],[f52,f59])).

fof(f59,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f49,f34])).

fof(f34,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X0) != k3_tarski(k2_tarski(X1,X2))
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_xboole_0 = X2 ) ),
    inference(definition_unfolding,[],[f50,f37,f42])).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f174,plain,(
    ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | ~ spl3_4 ),
    inference(resolution,[],[f101,f32])).

fof(f32,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f101,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl3_4
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f172,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl3_8 ),
    inference(resolution,[],[f168,f33])).

fof(f33,plain,(
    v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f168,plain,
    ( ~ v1_zfmisc_1(sK1)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl3_8
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f169,plain,
    ( spl3_4
    | ~ spl3_8
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f164,f120,f95,f166,f99])).

fof(f95,plain,
    ( spl3_3
  <=> k6_domain_1(sK1,sK2(sK1)) = k2_tarski(sK2(sK1),sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f164,plain,
    ( ~ v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1)
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(trivial_inequality_removal,[],[f163])).

fof(f163,plain,
    ( sK1 != sK1
    | ~ v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1)
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(superposition,[],[f160,f39])).

fof(f39,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK2(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK2(X0)) = X0
            & m1_subset_1(sK2(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK2(X0)) = X0
        & m1_subset_1(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(f160,plain,
    ( sK1 != k6_domain_1(sK1,sK2(sK1))
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(superposition,[],[f121,f97])).

fof(f97,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k2_tarski(sK2(sK1),sK2(sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f121,plain,
    ( ! [X7] : sK1 != k2_tarski(X7,X7)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f120])).

fof(f149,plain,(
    ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | ~ spl3_6 ),
    inference(trivial_inequality_removal,[],[f146])).

fof(f146,plain,
    ( sK0 != sK0
    | ~ spl3_6 ),
    inference(superposition,[],[f35,f118])).

fof(f118,plain,
    ( sK0 = sK1
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f35,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f135,plain,(
    ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl3_5 ),
    inference(trivial_inequality_removal,[],[f133])).

fof(f133,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_5 ),
    inference(resolution,[],[f123,f84])).

fof(f123,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f32,f114])).

fof(f114,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f112])).

fof(f102,plain,
    ( spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f91,f99,f95])).

fof(f91,plain,
    ( v1_xboole_0(sK1)
    | k6_domain_1(sK1,sK2(sK1)) = k2_tarski(sK2(sK1),sK2(sK1)) ),
    inference(resolution,[],[f90,f33])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,sK2(X0)) = k2_tarski(sK2(X0),sK2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK2(X0)) = k2_tarski(sK2(X0),sK2(X0))
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f53,f38])).

fof(f38,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f45,f37])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:09:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (4365)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (4366)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (4358)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (4375)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.50  % (4365)Refutation not found, incomplete strategy% (4365)------------------------------
% 0.20/0.50  % (4365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (4366)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (4357)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.50  % (4365)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (4365)Memory used [KB]: 10618
% 0.20/0.50  % (4365)Time elapsed: 0.099 s
% 0.20/0.50  % (4365)------------------------------
% 0.20/0.50  % (4365)------------------------------
% 0.20/0.51  % (4356)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f186,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f102,f135,f149,f169,f172,f174,f176,f185])).
% 0.20/0.51  fof(f185,plain,(
% 0.20/0.51    ~spl3_2),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f184])).
% 0.20/0.51  fof(f184,plain,(
% 0.20/0.51    $false | ~spl3_2),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f183])).
% 0.20/0.51  fof(f183,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0 | ~spl3_2),
% 0.20/0.51    inference(resolution,[],[f177,f84])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    ( ! [X0] : (v1_xboole_0(X0) | k1_xboole_0 != X0) )),
% 0.20/0.51    inference(resolution,[],[f79,f83])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | v1_xboole_0(X1)) )),
% 0.20/0.51    inference(resolution,[],[f81,f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.20/0.51    inference(flattening,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    ( ! [X2] : (r1_xboole_0(X2,k1_xboole_0)) )),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f80])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    ( ! [X2] : (X2 != X2 | r1_xboole_0(X2,k1_xboole_0)) )),
% 0.20/0.51    inference(superposition,[],[f47,f77])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 0.20/0.51    inference(forward_demodulation,[],[f73,f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X0] : (k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0) )),
% 0.20/0.51    inference(superposition,[],[f51,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X0] : (k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0) )),
% 0.20/0.51    inference(definition_unfolding,[],[f36,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k3_tarski(k2_tarski(k1_xboole_0,X2))) )),
% 0.20/0.51    inference(superposition,[],[f52,f55])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0)))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f43,f42,f42])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.51    inference(nnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    ( ! [X1] : (r1_tarski(X1,k1_xboole_0) | k1_xboole_0 != X1) )),
% 0.20/0.51    inference(superposition,[],[f48,f77])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.51    inference(nnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.51  fof(f177,plain,(
% 0.20/0.51    ~v1_xboole_0(k1_xboole_0) | ~spl3_2),
% 0.20/0.51    inference(backward_demodulation,[],[f31,f69])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    k1_xboole_0 = sK0 | ~spl3_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f68])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    spl3_2 <=> k1_xboole_0 = sK0),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ~v1_xboole_0(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    (sK0 != sK1 & r1_tarski(sK0,sK1) & v1_zfmisc_1(sK1) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f23,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (sK0 != X1 & r1_tarski(sK0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ? [X1] : (sK0 != X1 & r1_tarski(sK0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (sK0 != sK1 & r1_tarski(sK0,sK1) & v1_zfmisc_1(sK1) & ~v1_xboole_0(sK1))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.51    inference(flattening,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,negated_conjecture,(
% 0.20/0.51    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.20/0.51    inference(negated_conjecture,[],[f12])).
% 0.20/0.51  fof(f12,conjecture,(
% 0.20/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.20/0.51  fof(f176,plain,(
% 0.20/0.51    spl3_5 | spl3_6 | spl3_2 | spl3_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f159,f120,f68,f116,f112])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    spl3_5 <=> k1_xboole_0 = sK1),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    spl3_6 <=> sK0 = sK1),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    spl3_7 <=> ! [X7] : sK1 != k2_tarski(X7,X7)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.51  fof(f159,plain,(
% 0.20/0.51    ( ! [X0] : (k2_tarski(X0,X0) != sK1 | k1_xboole_0 = sK0 | sK0 = sK1 | k1_xboole_0 = sK1) )),
% 0.20/0.51    inference(superposition,[],[f54,f76])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    sK1 = k3_tarski(k2_tarski(sK0,sK1))),
% 0.20/0.51    inference(forward_demodulation,[],[f75,f41])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    sK1 = k3_tarski(k2_tarski(sK1,sK0))),
% 0.20/0.51    inference(forward_demodulation,[],[f72,f51])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    k3_tarski(k2_tarski(sK1,sK0)) = k3_tarski(k2_tarski(sK1,k1_xboole_0))),
% 0.20/0.51    inference(superposition,[],[f52,f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.20/0.51    inference(resolution,[],[f49,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    r1_tarski(sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f30])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k2_tarski(X0,X0) != k3_tarski(k2_tarski(X1,X2)) | k1_xboole_0 = X1 | X1 = X2 | k1_xboole_0 = X2) )),
% 0.20/0.51    inference(definition_unfolding,[],[f50,f37,f42])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k1_tarski(X0) != k2_xboole_0(X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k1_tarski(X0) != k2_xboole_0(X1,X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 0.20/0.51  fof(f174,plain,(
% 0.20/0.51    ~spl3_4),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f173])).
% 0.20/0.51  fof(f173,plain,(
% 0.20/0.51    $false | ~spl3_4),
% 0.20/0.51    inference(resolution,[],[f101,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ~v1_xboole_0(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    v1_xboole_0(sK1) | ~spl3_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f99])).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    spl3_4 <=> v1_xboole_0(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.51  fof(f172,plain,(
% 0.20/0.51    spl3_8),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f170])).
% 0.20/0.51  fof(f170,plain,(
% 0.20/0.51    $false | spl3_8),
% 0.20/0.51    inference(resolution,[],[f168,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    v1_zfmisc_1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f168,plain,(
% 0.20/0.51    ~v1_zfmisc_1(sK1) | spl3_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f166])).
% 0.20/0.51  fof(f166,plain,(
% 0.20/0.51    spl3_8 <=> v1_zfmisc_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.51  fof(f169,plain,(
% 0.20/0.51    spl3_4 | ~spl3_8 | ~spl3_3 | ~spl3_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f164,f120,f95,f166,f99])).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    spl3_3 <=> k6_domain_1(sK1,sK2(sK1)) = k2_tarski(sK2(sK1),sK2(sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.51  fof(f164,plain,(
% 0.20/0.51    ~v1_zfmisc_1(sK1) | v1_xboole_0(sK1) | (~spl3_3 | ~spl3_7)),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f163])).
% 0.20/0.51  fof(f163,plain,(
% 0.20/0.51    sK1 != sK1 | ~v1_zfmisc_1(sK1) | v1_xboole_0(sK1) | (~spl3_3 | ~spl3_7)),
% 0.20/0.51    inference(superposition,[],[f160,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X0] : (k6_domain_1(X0,sK2(X0)) = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.20/0.51    inference(rectify,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).
% 0.20/0.51  fof(f160,plain,(
% 0.20/0.51    sK1 != k6_domain_1(sK1,sK2(sK1)) | (~spl3_3 | ~spl3_7)),
% 0.20/0.51    inference(superposition,[],[f121,f97])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    k6_domain_1(sK1,sK2(sK1)) = k2_tarski(sK2(sK1),sK2(sK1)) | ~spl3_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f95])).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    ( ! [X7] : (sK1 != k2_tarski(X7,X7)) ) | ~spl3_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f120])).
% 0.20/0.51  fof(f149,plain,(
% 0.20/0.51    ~spl3_6),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f148])).
% 0.20/0.51  fof(f148,plain,(
% 0.20/0.51    $false | ~spl3_6),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f146])).
% 0.20/0.51  fof(f146,plain,(
% 0.20/0.51    sK0 != sK0 | ~spl3_6),
% 0.20/0.51    inference(superposition,[],[f35,f118])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    sK0 = sK1 | ~spl3_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f116])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    sK0 != sK1),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f135,plain,(
% 0.20/0.51    ~spl3_5),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f134])).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    $false | ~spl3_5),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f133])).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0 | ~spl3_5),
% 0.20/0.51    inference(resolution,[],[f123,f84])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    ~v1_xboole_0(k1_xboole_0) | ~spl3_5),
% 0.20/0.51    inference(backward_demodulation,[],[f32,f114])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | ~spl3_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f112])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    spl3_3 | spl3_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f91,f99,f95])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    v1_xboole_0(sK1) | k6_domain_1(sK1,sK2(sK1)) = k2_tarski(sK2(sK1),sK2(sK1))),
% 0.20/0.51    inference(resolution,[],[f90,f33])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_zfmisc_1(X0) | v1_xboole_0(X0) | k6_domain_1(X0,sK2(X0)) = k2_tarski(sK2(X0),sK2(X0))) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f89])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    ( ! [X0] : (k6_domain_1(X0,sK2(X0)) = k2_tarski(sK2(X0),sK2(X0)) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.51    inference(resolution,[],[f53,f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(sK2(X0),X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f45,f37])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.51    inference(flattening,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (4366)------------------------------
% 0.20/0.51  % (4366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (4366)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (4366)Memory used [KB]: 6268
% 0.20/0.51  % (4366)Time elapsed: 0.086 s
% 0.20/0.51  % (4366)------------------------------
% 0.20/0.51  % (4366)------------------------------
% 0.20/0.51  % (4352)Success in time 0.157 s
%------------------------------------------------------------------------------
