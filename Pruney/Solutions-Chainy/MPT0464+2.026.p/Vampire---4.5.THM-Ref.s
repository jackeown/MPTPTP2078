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
% DateTime   : Thu Dec  3 12:47:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 250 expanded)
%              Number of leaves         :   24 (  94 expanded)
%              Depth                    :   11
%              Number of atoms          :  197 ( 492 expanded)
%              Number of equality atoms :   18 ( 129 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f145,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f96,f99,f101,f103,f107,f130,f132,f144])).

fof(f144,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | spl3_10 ),
    inference(resolution,[],[f137,f129])).

fof(f129,plain,
    ( ~ r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK2)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl3_10
  <=> r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f137,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X1) ),
    inference(forward_demodulation,[],[f135,f51])).

fof(f51,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f34,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f41,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f135,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X1,X1,X1,X1,X1))) ),
    inference(superposition,[],[f53,f51])).

fof(f53,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_tarski(k3_enumset1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X2)))),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f42,f48,f49,f49,f48])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f47])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f42,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f132,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | spl3_9 ),
    inference(resolution,[],[f125,f30])).

fof(f30,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

fof(f125,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl3_9
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f130,plain,
    ( ~ spl3_3
    | ~ spl3_9
    | ~ spl3_5
    | ~ spl3_10
    | spl3_2 ),
    inference(avatar_split_clause,[],[f110,f75,f127,f89,f123,f81])).

fof(f81,plain,
    ( spl3_3
  <=> v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f89,plain,
    ( spl3_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f75,plain,
    ( spl3_2
  <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f110,plain,
    ( ~ r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK2)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)))
    | spl3_2 ),
    inference(resolution,[],[f77,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

fof(f77,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f107,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f95,f52])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f35,f49])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f95,plain,
    ( ~ r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK1)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl3_6
  <=> r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f103,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f91,f28])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f91,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f101,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f87,f29])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f87,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f99,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f97,f29])).

fof(f97,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_3 ),
    inference(resolution,[],[f83,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f56,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f56,plain,(
    ! [X0,X1] : m1_subset_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f52,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

% (18378)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
fof(f27,plain,(
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

fof(f83,plain,
    ( ~ v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f96,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_1 ),
    inference(avatar_split_clause,[],[f79,f71,f93,f89,f85,f81])).

fof(f71,plain,
    ( spl3_1
  <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f79,plain,
    ( ~ r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)))
    | spl3_1 ),
    inference(resolution,[],[f73,f32])).

fof(f73,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f78,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f69,f75,f71])).

fof(f69,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2))
    | ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f50,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f49])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f50,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k3_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))) ),
    inference(definition_unfolding,[],[f31,f49,f49])).

fof(f31,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:41:37 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.42  % (18381)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (18373)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (18371)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (18373)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f145,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f78,f96,f99,f101,f103,f107,f130,f132,f144])).
% 0.22/0.48  fof(f144,plain,(
% 0.22/0.48    spl3_10),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f140])).
% 0.22/0.48  fof(f140,plain,(
% 0.22/0.48    $false | spl3_10),
% 0.22/0.48    inference(resolution,[],[f137,f129])).
% 0.22/0.48  fof(f129,plain,(
% 0.22/0.48    ~r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK2) | spl3_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f127])).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    spl3_10 <=> r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.48  fof(f137,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X1)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f135,f51])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0) )),
% 0.22/0.48    inference(definition_unfolding,[],[f34,f48])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f37,f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f38,f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f41,f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.48    inference(rectify,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.22/0.48  fof(f135,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X1,X1,X1,X1,X1)))) )),
% 0.22/0.48    inference(superposition,[],[f53,f51])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k3_enumset1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X2)))),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f42,f48,f49,f49,f48])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f36,f47])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    spl3_9),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f131])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    $false | spl3_9),
% 0.22/0.48    inference(resolution,[],[f125,f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    v1_relat_1(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ((~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f25,f24,f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,negated_conjecture,(
% 0.22/0.48    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 0.22/0.48    inference(negated_conjecture,[],[f14])).
% 0.22/0.48  fof(f14,conjecture,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    ~v1_relat_1(sK2) | spl3_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f123])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    spl3_9 <=> v1_relat_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.48  fof(f130,plain,(
% 0.22/0.48    ~spl3_3 | ~spl3_9 | ~spl3_5 | ~spl3_10 | spl3_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f110,f75,f127,f89,f123,f81])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    spl3_3 <=> v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    spl3_5 <=> v1_relat_1(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    spl3_2 <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.48  fof(f110,plain,(
% 0.22/0.48    ~r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK2) | ~v1_relat_1(sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))) | spl3_2),
% 0.22/0.48    inference(resolution,[],[f77,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) | spl3_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f75])).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    spl3_6),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f106])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    $false | spl3_6),
% 0.22/0.48    inference(resolution,[],[f95,f52])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X0)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f35,f49])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    ~r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK1) | spl3_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f93])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    spl3_6 <=> r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    spl3_5),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f102])).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    $false | spl3_5),
% 0.22/0.48    inference(resolution,[],[f91,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    v1_relat_1(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    ~v1_relat_1(sK0) | spl3_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f89])).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    spl3_4),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f100])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    $false | spl3_4),
% 0.22/0.48    inference(resolution,[],[f87,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    v1_relat_1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    ~v1_relat_1(sK1) | spl3_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f85])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    spl3_4 <=> v1_relat_1(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    spl3_3),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f98])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    $false | spl3_3),
% 0.22/0.48    inference(resolution,[],[f97,f29])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    ~v1_relat_1(sK1) | spl3_3),
% 0.22/0.48    inference(resolution,[],[f83,f57])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(resolution,[],[f56,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_subset_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(resolution,[],[f52,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  % (18378)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.48    inference(nnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    ~v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))) | spl3_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f81])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | spl3_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f79,f71,f93,f89,f85,f81])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    spl3_1 <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    ~r1_tarski(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2)),sK1) | ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))) | spl3_1),
% 0.22/0.48    inference(resolution,[],[f73,f32])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) | spl3_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f71])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    ~spl3_1 | ~spl3_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f69,f75,f71])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) | ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))),
% 0.22/0.48    inference(resolution,[],[f50,f55])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f44,f49])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(flattening,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k3_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))))),
% 0.22/0.48    inference(definition_unfolding,[],[f31,f49,f49])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (18373)------------------------------
% 0.22/0.48  % (18373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (18373)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (18373)Memory used [KB]: 6140
% 0.22/0.48  % (18373)Time elapsed: 0.053 s
% 0.22/0.48  % (18373)------------------------------
% 0.22/0.48  % (18373)------------------------------
% 0.22/0.48  % (18377)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (18370)Success in time 0.115 s
%------------------------------------------------------------------------------
