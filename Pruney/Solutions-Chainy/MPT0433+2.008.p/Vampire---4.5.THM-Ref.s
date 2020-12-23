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
% DateTime   : Thu Dec  3 12:46:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 389 expanded)
%              Number of leaves         :   22 ( 139 expanded)
%              Depth                    :   11
%              Number of atoms          :  182 ( 556 expanded)
%              Number of equality atoms :   26 ( 279 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f264,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f172,f181,f195,f197,f201,f241,f263])).

fof(f263,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | spl2_6 ),
    inference(resolution,[],[f176,f120])).

fof(f120,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),X0) ),
    inference(superposition,[],[f114,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f31,f41,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f114,plain,(
    ! [X8,X9] : r1_tarski(k1_setfam_1(k2_enumset1(X8,X8,X8,X9)),X8) ),
    inference(superposition,[],[f54,f101])).

fof(f101,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) = X0 ),
    inference(forward_demodulation,[],[f48,f47])).

fof(f48,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f35,f42,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f41])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f41])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0))) ),
    inference(superposition,[],[f46,f47])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f30,f42])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f176,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl2_6
  <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f241,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f163,f114])).

fof(f163,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl2_3
  <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f201,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | spl2_4 ),
    inference(resolution,[],[f199,f25])).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).

fof(f199,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_4 ),
    inference(resolution,[],[f167,f111])).

fof(f111,plain,(
    ! [X2,X3] :
      ( v1_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f56,f101])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1)))
      | v1_relat_1(X1) ) ),
    inference(resolution,[],[f54,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f29,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f167,plain,
    ( ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl2_4
  <=> v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f197,plain,(
    spl2_7 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | spl2_7 ),
    inference(resolution,[],[f180,f26])).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f180,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl2_7
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f195,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | spl2_5 ),
    inference(resolution,[],[f171,f25])).

fof(f171,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl2_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f181,plain,
    ( ~ spl2_6
    | ~ spl2_4
    | ~ spl2_7
    | spl2_2 ),
    inference(avatar_split_clause,[],[f155,f79,f178,f165,f174])).

fof(f79,plain,
    ( spl2_2
  <=> r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f155,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)
    | spl2_2 ),
    inference(resolution,[],[f127,f81])).

fof(f81,plain,
    ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f127,plain,(
    ! [X2,X3] :
      ( r1_tarski(k1_relat_1(X2),k1_relat_1(X3))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f90,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f42])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f90,plain,(
    ! [X8,X9] :
      ( r1_tarski(k1_relat_1(X8),k1_relat_1(k3_tarski(k2_enumset1(X8,X8,X8,X9))))
      | ~ v1_relat_1(X9)
      | ~ v1_relat_1(X8) ) ),
    inference(superposition,[],[f46,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f28,f42,f42])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

fof(f172,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | spl2_1 ),
    inference(avatar_split_clause,[],[f154,f75,f169,f165,f161])).

fof(f75,plain,
    ( spl2_1
  <=> r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f154,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0)
    | spl2_1 ),
    inference(resolution,[],[f127,f77])).

fof(f77,plain,
    ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f82,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f71,f79,f75])).

fof(f71,plain,
    ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0)) ),
    inference(resolution,[],[f50,f44])).

fof(f44,plain,(
    ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f27,f43,f43])).

fof(f27,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f43])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.44  % (15318)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (15314)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (15316)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (15325)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (15316)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (15317)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (15324)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f264,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f82,f172,f181,f195,f197,f201,f241,f263])).
% 0.20/0.48  fof(f263,plain,(
% 0.20/0.48    spl2_6),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f262])).
% 0.20/0.48  fof(f262,plain,(
% 0.20/0.48    $false | spl2_6),
% 0.20/0.48    inference(resolution,[],[f176,f120])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),X0)) )),
% 0.20/0.48    inference(superposition,[],[f114,f47])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f31,f41,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f33,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    ( ! [X8,X9] : (r1_tarski(k1_setfam_1(k2_enumset1(X8,X8,X8,X9)),X8)) )),
% 0.20/0.48    inference(superposition,[],[f54,f101])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_tarski(k2_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) = X0) )),
% 0.20/0.48    inference(forward_demodulation,[],[f48,f47])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k4_xboole_0(X0,X1))) = X0) )),
% 0.20/0.48    inference(definition_unfolding,[],[f35,f42,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f32,f41])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f34,f41])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0)))) )),
% 0.20/0.48    inference(superposition,[],[f46,f47])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f30,f42])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.48  fof(f176,plain,(
% 0.20/0.48    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) | spl2_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f174])).
% 0.20/0.48  fof(f174,plain,(
% 0.20/0.48    spl2_6 <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.48  fof(f241,plain,(
% 0.20/0.48    spl2_3),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f240])).
% 0.20/0.48  fof(f240,plain,(
% 0.20/0.48    $false | spl2_3),
% 0.20/0.48    inference(resolution,[],[f163,f114])).
% 0.20/0.48  fof(f163,plain,(
% 0.20/0.48    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) | spl2_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f161])).
% 0.20/0.48  fof(f161,plain,(
% 0.20/0.48    spl2_3 <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.48  fof(f201,plain,(
% 0.20/0.48    spl2_4),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f200])).
% 0.20/0.48  fof(f200,plain,(
% 0.20/0.48    $false | spl2_4),
% 0.20/0.48    inference(resolution,[],[f199,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    v1_relat_1(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f22,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,negated_conjecture,(
% 0.20/0.48    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 0.20/0.48    inference(negated_conjecture,[],[f13])).
% 0.20/0.48  fof(f13,conjecture,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).
% 0.20/0.48  fof(f199,plain,(
% 0.20/0.48    ~v1_relat_1(sK0) | spl2_4),
% 0.20/0.48    inference(resolution,[],[f167,f111])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    ( ! [X2,X3] : (v1_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(superposition,[],[f56,f101])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1))) | v1_relat_1(X1)) )),
% 0.20/0.48    inference(resolution,[],[f54,f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) )),
% 0.20/0.48    inference(resolution,[],[f29,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.48    inference(nnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.48  fof(f167,plain,(
% 0.20/0.48    ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | spl2_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f165])).
% 0.20/0.48  fof(f165,plain,(
% 0.20/0.48    spl2_4 <=> v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.48  fof(f197,plain,(
% 0.20/0.48    spl2_7),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f196])).
% 0.20/0.48  fof(f196,plain,(
% 0.20/0.48    $false | spl2_7),
% 0.20/0.48    inference(resolution,[],[f180,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    v1_relat_1(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f180,plain,(
% 0.20/0.48    ~v1_relat_1(sK1) | spl2_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f178])).
% 0.20/0.48  fof(f178,plain,(
% 0.20/0.48    spl2_7 <=> v1_relat_1(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.48  fof(f195,plain,(
% 0.20/0.48    spl2_5),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f194])).
% 0.20/0.48  fof(f194,plain,(
% 0.20/0.48    $false | spl2_5),
% 0.20/0.48    inference(resolution,[],[f171,f25])).
% 0.20/0.48  fof(f171,plain,(
% 0.20/0.48    ~v1_relat_1(sK0) | spl2_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f169])).
% 0.20/0.48  fof(f169,plain,(
% 0.20/0.48    spl2_5 <=> v1_relat_1(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.48  fof(f181,plain,(
% 0.20/0.48    ~spl2_6 | ~spl2_4 | ~spl2_7 | spl2_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f155,f79,f178,f165,f174])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    spl2_2 <=> r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.48  fof(f155,plain,(
% 0.20/0.48    ~v1_relat_1(sK1) | ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) | spl2_2),
% 0.20/0.48    inference(resolution,[],[f127,f81])).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    ~r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1)) | spl2_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f79])).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    ( ! [X2,X3] : (r1_tarski(k1_relat_1(X2),k1_relat_1(X3)) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~r1_tarski(X2,X3)) )),
% 0.20/0.48    inference(superposition,[],[f90,f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f36,f42])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    ( ! [X8,X9] : (r1_tarski(k1_relat_1(X8),k1_relat_1(k3_tarski(k2_enumset1(X8,X8,X8,X9)))) | ~v1_relat_1(X9) | ~v1_relat_1(X8)) )),
% 0.20/0.48    inference(superposition,[],[f46,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f28,f42,f42])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).
% 0.20/0.48  fof(f172,plain,(
% 0.20/0.48    ~spl2_3 | ~spl2_4 | ~spl2_5 | spl2_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f154,f75,f169,f165,f161])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    spl2_1 <=> r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.48  fof(f154,plain,(
% 0.20/0.48    ~v1_relat_1(sK0) | ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) | spl2_1),
% 0.20/0.48    inference(resolution,[],[f127,f77])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    ~r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0)) | spl2_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f75])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    ~spl2_1 | ~spl2_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f71,f79,f75])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    ~r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0))),
% 0.20/0.48    inference(resolution,[],[f50,f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ~r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))))),
% 0.20/0.48    inference(definition_unfolding,[],[f27,f43,f43])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f40,f43])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(flattening,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (15316)------------------------------
% 0.20/0.48  % (15316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (15316)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (15316)Memory used [KB]: 6268
% 0.20/0.48  % (15316)Time elapsed: 0.060 s
% 0.20/0.48  % (15316)------------------------------
% 0.20/0.48  % (15316)------------------------------
% 0.20/0.48  % (15311)Success in time 0.12 s
%------------------------------------------------------------------------------
