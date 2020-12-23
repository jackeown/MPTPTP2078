%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 155 expanded)
%              Number of leaves         :   25 (  65 expanded)
%              Depth                    :    7
%              Number of atoms          :  274 ( 462 expanded)
%              Number of equality atoms :   26 (  43 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f133,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f54,f59,f64,f68,f76,f80,f87,f93,f97,f106,f114,f124,f132])).

fof(f132,plain,
    ( ~ spl2_2
    | ~ spl2_5
    | ~ spl2_8
    | spl2_11
    | ~ spl2_15 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_8
    | spl2_11
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f130,f48])).

fof(f48,plain,
    ( v1_zfmisc_1(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl2_2
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f130,plain,
    ( ~ v1_zfmisc_1(sK0)
    | ~ spl2_5
    | ~ spl2_8
    | spl2_11
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f129,f63])).

fof(f63,plain,
    ( v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl2_5
  <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f129,plain,
    ( ~ v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    | ~ v1_zfmisc_1(sK0)
    | ~ spl2_8
    | spl2_11
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f125,f92])).

fof(f92,plain,
    ( ~ v1_xboole_0(k6_domain_1(sK0,sK1))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl2_11
  <=> v1_xboole_0(k6_domain_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f125,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    | ~ v1_zfmisc_1(sK0)
    | ~ spl2_8
    | ~ spl2_15 ),
    inference(resolution,[],[f123,f75])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_xboole_0(X1)
        | ~ v1_subset_1(X1,X0)
        | ~ v1_zfmisc_1(X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( ~ v1_subset_1(X1,X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_zfmisc_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f123,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl2_15
  <=> m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f124,plain,
    ( spl2_15
    | ~ spl2_4
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f119,f100,f84,f56,f121])).

fof(f56,plain,
    ( spl2_4
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f84,plain,
    ( spl2_10
  <=> k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f100,plain,
    ( spl2_13
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | m1_subset_1(k1_enumset1(sK1,sK1,X0),k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f119,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl2_4
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f118,f86])).

fof(f86,plain,
    ( k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f84])).

fof(f118,plain,
    ( m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(sK0))
    | ~ spl2_4
    | ~ spl2_13 ),
    inference(resolution,[],[f101,f58])).

fof(f58,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | m1_subset_1(k1_enumset1(sK1,sK1,X0),k1_zfmisc_1(sK0)) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f100])).

fof(f114,plain,
    ( spl2_1
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl2_1
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f107,f53])).

fof(f53,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl2_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f107,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl2_1
    | ~ spl2_14 ),
    inference(backward_demodulation,[],[f43,f105])).

fof(f105,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl2_14
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f43,plain,
    ( ~ v1_xboole_0(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl2_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f106,plain,
    ( spl2_13
    | spl2_14
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f98,f95,f56,f103,f100])).

fof(f95,plain,
    ( spl2_12
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k1_enumset1(X1,X1,X2),k1_zfmisc_1(X0))
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X2,X0)
        | ~ m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f98,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK0
        | ~ m1_subset_1(X0,sK0)
        | m1_subset_1(k1_enumset1(sK1,sK1,X0),k1_zfmisc_1(sK0)) )
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(resolution,[],[f96,f58])).

fof(f96,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X2,X0)
        | m1_subset_1(k1_enumset1(X1,X1,X2),k1_zfmisc_1(X0)) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f95])).

fof(f97,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f37,f95])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_enumset1(X1,X1,X2),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(definition_unfolding,[],[f33,f32])).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          | k1_xboole_0 = X0
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          | k1_xboole_0 = X0
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ( k1_xboole_0 != X0
           => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_subset_1)).

fof(f93,plain,
    ( ~ spl2_11
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f88,f84,f66,f90])).

fof(f66,plain,
    ( spl2_6
  <=> ! [X0] : ~ v1_xboole_0(k1_enumset1(X0,X0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f88,plain,
    ( ~ v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(superposition,[],[f67,f86])).

fof(f67,plain,
    ( ! [X0] : ~ v1_xboole_0(k1_enumset1(X0,X0,X0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f87,plain,
    ( spl2_10
    | spl2_1
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f82,f78,f56,f41,f84])).

fof(f78,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f82,plain,
    ( k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1)
    | spl2_1
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f81,f43])).

fof(f81,plain,
    ( k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1)
    | v1_xboole_0(sK0)
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(resolution,[],[f79,f58])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1)
        | v1_xboole_0(X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f78])).

fof(f80,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f38,f78])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f35,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f32])).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f76,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f39,f74])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0) ) ),
    inference(subsumption_resolution,[],[f31,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f68,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f36,f66])).

fof(f36,plain,(
    ! [X0] : ~ v1_xboole_0(k1_enumset1(X0,X0,X0)) ),
    inference(definition_unfolding,[],[f28,f35])).

fof(f28,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f64,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f25,f61])).

fof(f25,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK0)
          & v1_subset_1(k6_domain_1(sK0,X1),sK0)
          & m1_subset_1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f59,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f24,f56])).

fof(f24,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f27,f51])).

fof(f27,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f49,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f26,f46])).

fof(f26,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f23,f41])).

fof(f23,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:06:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (18162)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.44  % (18165)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.45  % (18162)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f133,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f44,f49,f54,f59,f64,f68,f76,f80,f87,f93,f97,f106,f114,f124,f132])).
% 0.21/0.45  fof(f132,plain,(
% 0.21/0.45    ~spl2_2 | ~spl2_5 | ~spl2_8 | spl2_11 | ~spl2_15),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f131])).
% 0.21/0.45  fof(f131,plain,(
% 0.21/0.45    $false | (~spl2_2 | ~spl2_5 | ~spl2_8 | spl2_11 | ~spl2_15)),
% 0.21/0.45    inference(subsumption_resolution,[],[f130,f48])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    v1_zfmisc_1(sK0) | ~spl2_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f46])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    spl2_2 <=> v1_zfmisc_1(sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.45  fof(f130,plain,(
% 0.21/0.45    ~v1_zfmisc_1(sK0) | (~spl2_5 | ~spl2_8 | spl2_11 | ~spl2_15)),
% 0.21/0.45    inference(subsumption_resolution,[],[f129,f63])).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    v1_subset_1(k6_domain_1(sK0,sK1),sK0) | ~spl2_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f61])).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    spl2_5 <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.45  fof(f129,plain,(
% 0.21/0.45    ~v1_subset_1(k6_domain_1(sK0,sK1),sK0) | ~v1_zfmisc_1(sK0) | (~spl2_8 | spl2_11 | ~spl2_15)),
% 0.21/0.45    inference(subsumption_resolution,[],[f125,f92])).
% 0.21/0.45  fof(f92,plain,(
% 0.21/0.45    ~v1_xboole_0(k6_domain_1(sK0,sK1)) | spl2_11),
% 0.21/0.45    inference(avatar_component_clause,[],[f90])).
% 0.21/0.45  fof(f90,plain,(
% 0.21/0.45    spl2_11 <=> v1_xboole_0(k6_domain_1(sK0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.45  fof(f125,plain,(
% 0.21/0.45    v1_xboole_0(k6_domain_1(sK0,sK1)) | ~v1_subset_1(k6_domain_1(sK0,sK1),sK0) | ~v1_zfmisc_1(sK0) | (~spl2_8 | ~spl2_15)),
% 0.21/0.45    inference(resolution,[],[f123,f75])).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~v1_zfmisc_1(X0)) ) | ~spl2_8),
% 0.21/0.45    inference(avatar_component_clause,[],[f74])).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    spl2_8 <=> ! [X1,X0] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.45  fof(f123,plain,(
% 0.21/0.45    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl2_15),
% 0.21/0.45    inference(avatar_component_clause,[],[f121])).
% 0.21/0.45  fof(f121,plain,(
% 0.21/0.45    spl2_15 <=> m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.45  fof(f124,plain,(
% 0.21/0.45    spl2_15 | ~spl2_4 | ~spl2_10 | ~spl2_13),
% 0.21/0.45    inference(avatar_split_clause,[],[f119,f100,f84,f56,f121])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    spl2_4 <=> m1_subset_1(sK1,sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    spl2_10 <=> k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.45  fof(f100,plain,(
% 0.21/0.45    spl2_13 <=> ! [X0] : (~m1_subset_1(X0,sK0) | m1_subset_1(k1_enumset1(sK1,sK1,X0),k1_zfmisc_1(sK0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.45  fof(f119,plain,(
% 0.21/0.45    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | (~spl2_4 | ~spl2_10 | ~spl2_13)),
% 0.21/0.45    inference(forward_demodulation,[],[f118,f86])).
% 0.21/0.45  fof(f86,plain,(
% 0.21/0.45    k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1) | ~spl2_10),
% 0.21/0.45    inference(avatar_component_clause,[],[f84])).
% 0.21/0.45  fof(f118,plain,(
% 0.21/0.45    m1_subset_1(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(sK0)) | (~spl2_4 | ~spl2_13)),
% 0.21/0.45    inference(resolution,[],[f101,f58])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    m1_subset_1(sK1,sK0) | ~spl2_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f56])).
% 0.21/0.45  fof(f101,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(X0,sK0) | m1_subset_1(k1_enumset1(sK1,sK1,X0),k1_zfmisc_1(sK0))) ) | ~spl2_13),
% 0.21/0.45    inference(avatar_component_clause,[],[f100])).
% 0.21/0.45  fof(f114,plain,(
% 0.21/0.45    spl2_1 | ~spl2_3 | ~spl2_14),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f113])).
% 0.21/0.45  fof(f113,plain,(
% 0.21/0.45    $false | (spl2_1 | ~spl2_3 | ~spl2_14)),
% 0.21/0.45    inference(subsumption_resolution,[],[f107,f53])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    v1_xboole_0(k1_xboole_0) | ~spl2_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f51])).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    spl2_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.45  fof(f107,plain,(
% 0.21/0.45    ~v1_xboole_0(k1_xboole_0) | (spl2_1 | ~spl2_14)),
% 0.21/0.45    inference(backward_demodulation,[],[f43,f105])).
% 0.21/0.45  fof(f105,plain,(
% 0.21/0.45    k1_xboole_0 = sK0 | ~spl2_14),
% 0.21/0.45    inference(avatar_component_clause,[],[f103])).
% 0.21/0.45  fof(f103,plain,(
% 0.21/0.45    spl2_14 <=> k1_xboole_0 = sK0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ~v1_xboole_0(sK0) | spl2_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    spl2_1 <=> v1_xboole_0(sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.45  fof(f106,plain,(
% 0.21/0.45    spl2_13 | spl2_14 | ~spl2_4 | ~spl2_12),
% 0.21/0.45    inference(avatar_split_clause,[],[f98,f95,f56,f103,f100])).
% 0.21/0.45  fof(f95,plain,(
% 0.21/0.45    spl2_12 <=> ! [X1,X0,X2] : (m1_subset_1(k1_enumset1(X1,X1,X2),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.45  fof(f98,plain,(
% 0.21/0.45    ( ! [X0] : (k1_xboole_0 = sK0 | ~m1_subset_1(X0,sK0) | m1_subset_1(k1_enumset1(sK1,sK1,X0),k1_zfmisc_1(sK0))) ) | (~spl2_4 | ~spl2_12)),
% 0.21/0.45    inference(resolution,[],[f96,f58])).
% 0.21/0.45  fof(f96,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,X0) | m1_subset_1(k1_enumset1(X1,X1,X2),k1_zfmisc_1(X0))) ) | ~spl2_12),
% 0.21/0.45    inference(avatar_component_clause,[],[f95])).
% 0.21/0.45  fof(f97,plain,(
% 0.21/0.45    spl2_12),
% 0.21/0.45    inference(avatar_split_clause,[],[f37,f95])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (m1_subset_1(k1_enumset1(X1,X1,X2),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f33,f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0,X1] : (! [X2] : (m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 0.21/0.45    inference(flattening,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0,X1] : (! [X2] : ((m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => (k1_xboole_0 != X0 => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_subset_1)).
% 0.21/0.45  fof(f93,plain,(
% 0.21/0.45    ~spl2_11 | ~spl2_6 | ~spl2_10),
% 0.21/0.45    inference(avatar_split_clause,[],[f88,f84,f66,f90])).
% 0.21/0.45  fof(f66,plain,(
% 0.21/0.45    spl2_6 <=> ! [X0] : ~v1_xboole_0(k1_enumset1(X0,X0,X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.45  fof(f88,plain,(
% 0.21/0.45    ~v1_xboole_0(k6_domain_1(sK0,sK1)) | (~spl2_6 | ~spl2_10)),
% 0.21/0.45    inference(superposition,[],[f67,f86])).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    ( ! [X0] : (~v1_xboole_0(k1_enumset1(X0,X0,X0))) ) | ~spl2_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f66])).
% 0.21/0.45  fof(f87,plain,(
% 0.21/0.45    spl2_10 | spl2_1 | ~spl2_4 | ~spl2_9),
% 0.21/0.45    inference(avatar_split_clause,[],[f82,f78,f56,f41,f84])).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    spl2_9 <=> ! [X1,X0] : (k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1) | (spl2_1 | ~spl2_4 | ~spl2_9)),
% 0.21/0.45    inference(subsumption_resolution,[],[f81,f43])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1) | v1_xboole_0(sK0) | (~spl2_4 | ~spl2_9)),
% 0.21/0.45    inference(resolution,[],[f79,f58])).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1) | v1_xboole_0(X0)) ) | ~spl2_9),
% 0.21/0.45    inference(avatar_component_clause,[],[f78])).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    spl2_9),
% 0.21/0.45    inference(avatar_split_clause,[],[f38,f78])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f34,f35])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f29,f32])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.45    inference(flattening,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    spl2_8),
% 0.21/0.45    inference(avatar_split_clause,[],[f39,f74])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f31,f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.21/0.45    inference(flattening,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.21/0.45  fof(f68,plain,(
% 0.21/0.45    spl2_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f36,f66])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ( ! [X0] : (~v1_xboole_0(k1_enumset1(X0,X0,X0))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f28,f35])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    spl2_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f25,f61])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f21,f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.45    inference(flattening,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,negated_conjecture,(
% 0.21/0.45    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.45    inference(negated_conjecture,[],[f9])).
% 0.21/0.45  fof(f9,conjecture,(
% 0.21/0.45    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    spl2_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f24,f56])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    m1_subset_1(sK1,sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    spl2_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f27,f51])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    v1_xboole_0(k1_xboole_0)),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    v1_xboole_0(k1_xboole_0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    spl2_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f26,f46])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    v1_zfmisc_1(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ~spl2_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f23,f41])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ~v1_xboole_0(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (18162)------------------------------
% 0.21/0.45  % (18162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (18162)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (18162)Memory used [KB]: 6140
% 0.21/0.45  % (18162)Time elapsed: 0.033 s
% 0.21/0.45  % (18162)------------------------------
% 0.21/0.45  % (18162)------------------------------
% 0.21/0.45  % (18154)Success in time 0.088 s
%------------------------------------------------------------------------------
