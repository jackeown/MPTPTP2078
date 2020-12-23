%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:25 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 148 expanded)
%              Number of leaves         :   23 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :  215 ( 303 expanded)
%              Number of equality atoms :   13 (  33 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f523,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f66,f176,f216,f218,f239,f241,f268,f522])).

fof(f522,plain,
    ( spl3_7
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f519])).

fof(f519,plain,
    ( $false
    | spl3_7
    | ~ spl3_11 ),
    inference(resolution,[],[f510,f187])).

fof(f187,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl3_11
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f510,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl3_7 ),
    inference(resolution,[],[f227,f52])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f37,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f227,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
        | ~ r1_tarski(k1_relat_1(sK2),X0) )
    | spl3_7 ),
    inference(resolution,[],[f171,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f171,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl3_7
  <=> r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f268,plain,
    ( spl3_8
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | spl3_8
    | ~ spl3_14 ),
    inference(resolution,[],[f243,f200])).

fof(f200,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl3_14
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f243,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl3_8 ),
    inference(resolution,[],[f175,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f49])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f175,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl3_8
  <=> r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f241,plain,(
    spl3_19 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | spl3_19 ),
    inference(resolution,[],[f238,f70])).

fof(f70,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f45,f32])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f238,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | spl3_19 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl3_19
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f239,plain,
    ( ~ spl3_19
    | ~ spl3_2
    | spl3_11 ),
    inference(avatar_split_clause,[],[f233,f186,f61,f236])).

fof(f61,plain,
    ( spl3_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f233,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK0)
    | spl3_11 ),
    inference(resolution,[],[f188,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f40,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f188,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f186])).

fof(f218,plain,(
    spl3_16 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | spl3_16 ),
    inference(resolution,[],[f215,f71])).

fof(f71,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f46,f32])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f215,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl3_16
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f216,plain,
    ( ~ spl3_2
    | ~ spl3_16
    | spl3_14 ),
    inference(avatar_split_clause,[],[f210,f199,f213,f61])).

fof(f210,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | spl3_14 ),
    inference(resolution,[],[f201,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f201,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f199])).

fof(f176,plain,
    ( ~ spl3_2
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f146,f173,f169,f61])).

fof(f146,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | ~ r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f94,f50])).

fof(f50,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f33,f49])).

fof(f33,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),X1)
      | ~ r1_tarski(k2_relat_1(X0),X1)
      | ~ r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f54,f51])).

fof(f51,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f34,f49])).

fof(f34,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f66,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f59,f36])).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f59,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_1
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f64,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f55,f61,f57])).

fof(f55,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f35,f32])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:07:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (12633)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.46  % (12622)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (12627)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (12634)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (12636)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (12626)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (12629)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (12620)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (12637)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (12630)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (12624)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (12623)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (12625)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (12621)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (12628)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.51  % (12632)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  % (12635)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.25/0.52  % (12624)Refutation found. Thanks to Tanya!
% 1.25/0.52  % SZS status Theorem for theBenchmark
% 1.25/0.52  % (12631)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.25/0.53  % SZS output start Proof for theBenchmark
% 1.25/0.53  fof(f523,plain,(
% 1.25/0.53    $false),
% 1.25/0.53    inference(avatar_sat_refutation,[],[f64,f66,f176,f216,f218,f239,f241,f268,f522])).
% 1.25/0.53  fof(f522,plain,(
% 1.25/0.53    spl3_7 | ~spl3_11),
% 1.25/0.53    inference(avatar_contradiction_clause,[],[f519])).
% 1.25/0.53  fof(f519,plain,(
% 1.25/0.53    $false | (spl3_7 | ~spl3_11)),
% 1.25/0.53    inference(resolution,[],[f510,f187])).
% 1.25/0.53  fof(f187,plain,(
% 1.25/0.53    r1_tarski(k1_relat_1(sK2),sK0) | ~spl3_11),
% 1.25/0.53    inference(avatar_component_clause,[],[f186])).
% 1.25/0.53  fof(f186,plain,(
% 1.25/0.53    spl3_11 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.25/0.53  fof(f510,plain,(
% 1.25/0.53    ~r1_tarski(k1_relat_1(sK2),sK0) | spl3_7),
% 1.25/0.53    inference(resolution,[],[f227,f52])).
% 1.25/0.53  fof(f52,plain,(
% 1.25/0.53    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 1.25/0.53    inference(definition_unfolding,[],[f37,f49])).
% 1.25/0.53  fof(f49,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.25/0.53    inference(definition_unfolding,[],[f38,f39])).
% 1.25/0.53  fof(f39,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f5])).
% 1.25/0.53  fof(f5,axiom,(
% 1.25/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.25/0.53  fof(f38,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f6])).
% 1.25/0.53  fof(f6,axiom,(
% 1.25/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.25/0.53  fof(f37,plain,(
% 1.25/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f3])).
% 1.25/0.53  fof(f3,axiom,(
% 1.25/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.25/0.53  fof(f227,plain,(
% 1.25/0.53    ( ! [X0] : (~r1_tarski(X0,k3_tarski(k1_enumset1(sK0,sK0,sK1))) | ~r1_tarski(k1_relat_1(sK2),X0)) ) | spl3_7),
% 1.25/0.53    inference(resolution,[],[f171,f47])).
% 1.25/0.53  fof(f47,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f26])).
% 1.25/0.53  fof(f26,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.25/0.53    inference(flattening,[],[f25])).
% 1.25/0.53  fof(f25,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.25/0.53    inference(ennf_transformation,[],[f2])).
% 1.25/0.53  fof(f2,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.25/0.53  fof(f171,plain,(
% 1.25/0.53    ~r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) | spl3_7),
% 1.25/0.53    inference(avatar_component_clause,[],[f169])).
% 1.25/0.53  fof(f169,plain,(
% 1.25/0.53    spl3_7 <=> r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.25/0.53  fof(f268,plain,(
% 1.25/0.53    spl3_8 | ~spl3_14),
% 1.25/0.53    inference(avatar_contradiction_clause,[],[f265])).
% 1.25/0.53  fof(f265,plain,(
% 1.25/0.53    $false | (spl3_8 | ~spl3_14)),
% 1.25/0.53    inference(resolution,[],[f243,f200])).
% 1.25/0.53  fof(f200,plain,(
% 1.25/0.53    r1_tarski(k2_relat_1(sK2),sK1) | ~spl3_14),
% 1.25/0.53    inference(avatar_component_clause,[],[f199])).
% 1.25/0.53  fof(f199,plain,(
% 1.25/0.53    spl3_14 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.25/0.53  fof(f243,plain,(
% 1.25/0.53    ~r1_tarski(k2_relat_1(sK2),sK1) | spl3_8),
% 1.25/0.53    inference(resolution,[],[f175,f53])).
% 1.25/0.53  fof(f53,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 1.25/0.53    inference(definition_unfolding,[],[f44,f49])).
% 1.25/0.53  fof(f44,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f23])).
% 1.25/0.53  fof(f23,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.25/0.53    inference(ennf_transformation,[],[f1])).
% 1.25/0.53  fof(f1,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.25/0.53  fof(f175,plain,(
% 1.25/0.53    ~r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) | spl3_8),
% 1.25/0.53    inference(avatar_component_clause,[],[f173])).
% 1.25/0.53  fof(f173,plain,(
% 1.25/0.53    spl3_8 <=> r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.25/0.53  fof(f241,plain,(
% 1.25/0.53    spl3_19),
% 1.25/0.53    inference(avatar_contradiction_clause,[],[f240])).
% 1.25/0.53  fof(f240,plain,(
% 1.25/0.53    $false | spl3_19),
% 1.25/0.53    inference(resolution,[],[f238,f70])).
% 1.25/0.53  fof(f70,plain,(
% 1.25/0.53    v4_relat_1(sK2,sK0)),
% 1.25/0.53    inference(resolution,[],[f45,f32])).
% 1.25/0.53  fof(f32,plain,(
% 1.25/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.25/0.53    inference(cnf_transformation,[],[f30])).
% 1.25/0.53  fof(f30,plain,(
% 1.25/0.53    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.25/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f29])).
% 1.25/0.53  fof(f29,plain,(
% 1.25/0.53    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 1.25/0.53    introduced(choice_axiom,[])).
% 1.25/0.53  fof(f16,plain,(
% 1.25/0.53    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.53    inference(ennf_transformation,[],[f15])).
% 1.25/0.53  fof(f15,negated_conjecture,(
% 1.25/0.53    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 1.25/0.53    inference(negated_conjecture,[],[f14])).
% 1.25/0.53  fof(f14,conjecture,(
% 1.25/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).
% 1.25/0.53  fof(f45,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f24])).
% 1.25/0.53  fof(f24,plain,(
% 1.25/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.53    inference(ennf_transformation,[],[f13])).
% 1.25/0.53  fof(f13,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.25/0.53  fof(f238,plain,(
% 1.25/0.53    ~v4_relat_1(sK2,sK0) | spl3_19),
% 1.25/0.53    inference(avatar_component_clause,[],[f236])).
% 1.25/0.53  fof(f236,plain,(
% 1.25/0.53    spl3_19 <=> v4_relat_1(sK2,sK0)),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.25/0.53  fof(f239,plain,(
% 1.25/0.53    ~spl3_19 | ~spl3_2 | spl3_11),
% 1.25/0.53    inference(avatar_split_clause,[],[f233,f186,f61,f236])).
% 1.25/0.53  fof(f61,plain,(
% 1.25/0.53    spl3_2 <=> v1_relat_1(sK2)),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.25/0.53  fof(f233,plain,(
% 1.25/0.53    ~v1_relat_1(sK2) | ~v4_relat_1(sK2,sK0) | spl3_11),
% 1.25/0.53    inference(resolution,[],[f188,f75])).
% 1.25/0.53  fof(f75,plain,(
% 1.25/0.53    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 1.25/0.53    inference(duplicate_literal_removal,[],[f74])).
% 1.25/0.53  fof(f74,plain,(
% 1.25/0.53    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 1.25/0.53    inference(superposition,[],[f40,f43])).
% 1.25/0.53  fof(f43,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f22])).
% 1.25/0.53  fof(f22,plain,(
% 1.25/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.25/0.53    inference(flattening,[],[f21])).
% 1.25/0.53  fof(f21,plain,(
% 1.25/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.25/0.53    inference(ennf_transformation,[],[f11])).
% 1.25/0.53  fof(f11,axiom,(
% 1.25/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.25/0.53  fof(f40,plain,(
% 1.25/0.53    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f19])).
% 1.25/0.53  fof(f19,plain,(
% 1.25/0.53    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.25/0.53    inference(ennf_transformation,[],[f12])).
% 1.25/0.53  fof(f12,axiom,(
% 1.25/0.53    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 1.25/0.53  fof(f188,plain,(
% 1.25/0.53    ~r1_tarski(k1_relat_1(sK2),sK0) | spl3_11),
% 1.25/0.53    inference(avatar_component_clause,[],[f186])).
% 1.25/0.53  fof(f218,plain,(
% 1.25/0.53    spl3_16),
% 1.25/0.53    inference(avatar_contradiction_clause,[],[f217])).
% 1.25/0.53  fof(f217,plain,(
% 1.25/0.53    $false | spl3_16),
% 1.25/0.53    inference(resolution,[],[f215,f71])).
% 1.25/0.53  fof(f71,plain,(
% 1.25/0.53    v5_relat_1(sK2,sK1)),
% 1.25/0.53    inference(resolution,[],[f46,f32])).
% 1.25/0.53  fof(f46,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f24])).
% 1.25/0.53  fof(f215,plain,(
% 1.25/0.53    ~v5_relat_1(sK2,sK1) | spl3_16),
% 1.25/0.53    inference(avatar_component_clause,[],[f213])).
% 1.25/0.53  fof(f213,plain,(
% 1.25/0.53    spl3_16 <=> v5_relat_1(sK2,sK1)),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.25/0.53  fof(f216,plain,(
% 1.25/0.53    ~spl3_2 | ~spl3_16 | spl3_14),
% 1.25/0.53    inference(avatar_split_clause,[],[f210,f199,f213,f61])).
% 1.25/0.53  fof(f210,plain,(
% 1.25/0.53    ~v5_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | spl3_14),
% 1.25/0.53    inference(resolution,[],[f201,f41])).
% 1.25/0.53  fof(f41,plain,(
% 1.25/0.53    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f31])).
% 1.25/0.53  fof(f31,plain,(
% 1.25/0.53    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.25/0.53    inference(nnf_transformation,[],[f20])).
% 1.25/0.53  fof(f20,plain,(
% 1.25/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.25/0.53    inference(ennf_transformation,[],[f8])).
% 1.25/0.53  fof(f8,axiom,(
% 1.25/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.25/0.53  fof(f201,plain,(
% 1.25/0.53    ~r1_tarski(k2_relat_1(sK2),sK1) | spl3_14),
% 1.25/0.53    inference(avatar_component_clause,[],[f199])).
% 1.25/0.53  fof(f176,plain,(
% 1.25/0.53    ~spl3_2 | ~spl3_7 | ~spl3_8),
% 1.25/0.53    inference(avatar_split_clause,[],[f146,f173,f169,f61])).
% 1.25/0.53  fof(f146,plain,(
% 1.25/0.53    ~r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) | ~r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) | ~v1_relat_1(sK2)),
% 1.25/0.53    inference(resolution,[],[f94,f50])).
% 1.25/0.53  fof(f50,plain,(
% 1.25/0.53    ~r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))),
% 1.25/0.53    inference(definition_unfolding,[],[f33,f49])).
% 1.25/0.53  fof(f33,plain,(
% 1.25/0.53    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 1.25/0.53    inference(cnf_transformation,[],[f30])).
% 1.25/0.53  fof(f94,plain,(
% 1.25/0.53    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),X1) | ~r1_tarski(k2_relat_1(X0),X1) | ~r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 1.25/0.53    inference(superposition,[],[f54,f51])).
% 1.25/0.53  fof(f51,plain,(
% 1.25/0.53    ( ! [X0] : (k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.25/0.53    inference(definition_unfolding,[],[f34,f49])).
% 1.25/0.53  fof(f34,plain,(
% 1.25/0.53    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f17])).
% 1.25/0.53  fof(f17,plain,(
% 1.25/0.53    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.25/0.53    inference(ennf_transformation,[],[f9])).
% 1.25/0.53  fof(f9,axiom,(
% 1.25/0.53    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 1.25/0.53  fof(f54,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.25/0.53    inference(definition_unfolding,[],[f48,f49])).
% 1.25/0.53  fof(f48,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f28])).
% 1.25/0.53  fof(f28,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.25/0.53    inference(flattening,[],[f27])).
% 1.25/0.53  fof(f27,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.25/0.53    inference(ennf_transformation,[],[f4])).
% 1.25/0.53  fof(f4,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.25/0.53  fof(f66,plain,(
% 1.25/0.53    spl3_1),
% 1.25/0.53    inference(avatar_contradiction_clause,[],[f65])).
% 1.25/0.53  fof(f65,plain,(
% 1.25/0.53    $false | spl3_1),
% 1.25/0.53    inference(resolution,[],[f59,f36])).
% 1.25/0.53  fof(f36,plain,(
% 1.25/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f10])).
% 1.25/0.53  fof(f10,axiom,(
% 1.25/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.25/0.53  fof(f59,plain,(
% 1.25/0.53    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl3_1),
% 1.25/0.53    inference(avatar_component_clause,[],[f57])).
% 1.25/0.53  fof(f57,plain,(
% 1.25/0.53    spl3_1 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.25/0.53  fof(f64,plain,(
% 1.25/0.53    ~spl3_1 | spl3_2),
% 1.25/0.53    inference(avatar_split_clause,[],[f55,f61,f57])).
% 1.25/0.53  fof(f55,plain,(
% 1.25/0.53    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.25/0.53    inference(resolution,[],[f35,f32])).
% 1.25/0.53  fof(f35,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f18])).
% 1.25/0.53  fof(f18,plain,(
% 1.25/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.25/0.53    inference(ennf_transformation,[],[f7])).
% 1.25/0.53  fof(f7,axiom,(
% 1.25/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.25/0.53  % SZS output end Proof for theBenchmark
% 1.25/0.53  % (12624)------------------------------
% 1.25/0.53  % (12624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (12624)Termination reason: Refutation
% 1.25/0.53  
% 1.25/0.53  % (12624)Memory used [KB]: 6268
% 1.25/0.53  % (12624)Time elapsed: 0.103 s
% 1.25/0.53  % (12624)------------------------------
% 1.25/0.53  % (12624)------------------------------
% 1.38/0.53  % (12619)Success in time 0.172 s
%------------------------------------------------------------------------------
