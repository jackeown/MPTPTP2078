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
% DateTime   : Thu Dec  3 12:46:52 EST 2020

% Result     : Theorem 1.87s
% Output     : Refutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 459 expanded)
%              Number of leaves         :   19 ( 154 expanded)
%              Depth                    :   11
%              Number of atoms          :  182 ( 652 expanded)
%              Number of equality atoms :   29 ( 349 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f418,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f206,f301,f303,f328,f417])).

fof(f417,plain,
    ( spl2_2
    | ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f413])).

fof(f413,plain,
    ( $false
    | spl2_2
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f23,f204,f321,f52,f119,f180])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k1_relat_1(X1))
      | r1_tarski(X2,k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f150,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(X1,X1,X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f49,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f28,f42,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f42])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f150,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(X4,k1_relat_1(k3_tarski(k2_enumset1(X2,X2,X2,X3))))
      | ~ r1_tarski(X4,k1_relat_1(X3))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f50,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f26,f43,f43])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f43])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f119,plain,
    ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl2_2
  <=> r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f321,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),X0) ),
    inference(superposition,[],[f295,f47])).

fof(f295,plain,(
    ! [X4,X3] : r1_tarski(k1_setfam_1(k2_enumset1(X3,X3,X3,X4)),X3) ),
    inference(resolution,[],[f253,f52])).

fof(f253,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))
      | r1_tarski(X4,X2) ) ),
    inference(superposition,[],[f50,f207])).

fof(f207,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) = X0 ),
    inference(forward_demodulation,[],[f48,f47])).

fof(f48,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f32,f43,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f29,f42])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f204,plain,
    ( v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl2_5
  <=> v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

fof(f328,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | spl2_5 ),
    inference(unit_resulting_resolution,[],[f25,f52,f52,f205,f295,f139])).

fof(f139,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_tarski(X7,X4)
      | ~ v1_relat_1(X6)
      | v1_relat_1(X7)
      | ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f90,f49])).

fof(f90,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_tarski(k3_tarski(k2_enumset1(X4,X4,X4,X5)),X3)
      | ~ v1_relat_1(X3)
      | v1_relat_1(X2)
      | ~ r1_tarski(X2,X4) ) ),
    inference(resolution,[],[f86,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_tarski(k2_enumset1(X1,X1,X1,X0)))
      | ~ r1_tarski(X2,X1) ) ),
    inference(superposition,[],[f50,f47])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f61,f58])).

fof(f61,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_relat_1(k3_tarski(k2_enumset1(X5,X5,X5,X4)))
      | v1_relat_1(X3)
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f50,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f27,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f205,plain,
    ( ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f203])).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f303,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | spl2_4 ),
    inference(subsumption_resolution,[],[f25,f201])).

fof(f201,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl2_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f301,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | spl2_3 ),
    inference(unit_resulting_resolution,[],[f197,f52,f253])).

fof(f197,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl2_3
  <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f206,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | spl2_1 ),
    inference(avatar_split_clause,[],[f185,f113,f203,f199,f195])).

fof(f113,plain,
    ( spl2_1
  <=> r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f185,plain,
    ( ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0)
    | spl2_1 ),
    inference(resolution,[],[f184,f115])).

fof(f115,plain,
    ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f184,plain,(
    ! [X4,X5] :
      ( r1_tarski(k1_relat_1(X4),k1_relat_1(X5))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | ~ r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f180,f52])).

fof(f120,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f111,f117,f113])).

fof(f111,plain,
    ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0)) ),
    inference(resolution,[],[f45,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f44])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f45,plain,(
    ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f24,f44,f44])).

fof(f24,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:30:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (25797)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.48  % (25788)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.49  % (25780)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (25788)Refutation not found, incomplete strategy% (25788)------------------------------
% 0.20/0.50  % (25788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (25788)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (25788)Memory used [KB]: 1918
% 0.20/0.50  % (25788)Time elapsed: 0.063 s
% 0.20/0.50  % (25788)------------------------------
% 0.20/0.50  % (25788)------------------------------
% 0.20/0.51  % (25800)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (25781)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (25784)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (25784)Refutation not found, incomplete strategy% (25784)------------------------------
% 0.20/0.52  % (25784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25784)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (25784)Memory used [KB]: 10746
% 0.20/0.52  % (25784)Time elapsed: 0.108 s
% 0.20/0.52  % (25784)------------------------------
% 0.20/0.52  % (25784)------------------------------
% 0.20/0.52  % (25792)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.52  % (25778)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (25800)Refutation not found, incomplete strategy% (25800)------------------------------
% 0.20/0.52  % (25800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25800)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (25800)Memory used [KB]: 6268
% 0.20/0.52  % (25800)Time elapsed: 0.119 s
% 0.20/0.52  % (25800)------------------------------
% 0.20/0.52  % (25800)------------------------------
% 0.20/0.53  % (25775)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (25801)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (25803)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (25777)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (25779)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (25803)Refutation not found, incomplete strategy% (25803)------------------------------
% 0.20/0.53  % (25803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (25803)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (25803)Memory used [KB]: 1663
% 0.20/0.53  % (25803)Time elapsed: 0.131 s
% 0.20/0.53  % (25803)------------------------------
% 0.20/0.53  % (25803)------------------------------
% 0.20/0.53  % (25783)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.53  % (25773)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (25796)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.54  % (25802)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (25790)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (25802)Refutation not found, incomplete strategy% (25802)------------------------------
% 0.20/0.54  % (25802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (25802)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (25802)Memory used [KB]: 10746
% 0.20/0.54  % (25802)Time elapsed: 0.131 s
% 0.20/0.54  % (25802)------------------------------
% 0.20/0.54  % (25802)------------------------------
% 0.20/0.54  % (25794)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (25787)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (25790)Refutation not found, incomplete strategy% (25790)------------------------------
% 0.20/0.54  % (25790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (25786)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.54  % (25795)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (25785)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.55  % (25798)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.55  % (25793)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (25798)Refutation not found, incomplete strategy% (25798)------------------------------
% 0.20/0.55  % (25798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (25798)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (25798)Memory used [KB]: 10746
% 0.20/0.55  % (25798)Time elapsed: 0.142 s
% 0.20/0.55  % (25798)------------------------------
% 0.20/0.55  % (25798)------------------------------
% 0.20/0.55  % (25774)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.55  % (25789)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.55  % (25774)Refutation not found, incomplete strategy% (25774)------------------------------
% 0.20/0.55  % (25774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (25774)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (25774)Memory used [KB]: 1791
% 0.20/0.55  % (25774)Time elapsed: 0.148 s
% 0.20/0.55  % (25774)------------------------------
% 0.20/0.55  % (25774)------------------------------
% 0.20/0.55  % (25782)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.56  % (25790)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (25790)Memory used [KB]: 10618
% 0.20/0.56  % (25790)Time elapsed: 0.128 s
% 0.20/0.56  % (25790)------------------------------
% 0.20/0.56  % (25790)------------------------------
% 0.20/0.56  % (25799)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.56  % (25791)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.87/0.60  % (25787)Refutation found. Thanks to Tanya!
% 1.87/0.60  % SZS status Theorem for theBenchmark
% 2.01/0.62  % (25876)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.01/0.62  % SZS output start Proof for theBenchmark
% 2.01/0.62  fof(f418,plain,(
% 2.01/0.62    $false),
% 2.01/0.62    inference(avatar_sat_refutation,[],[f120,f206,f301,f303,f328,f417])).
% 2.01/0.62  fof(f417,plain,(
% 2.01/0.62    spl2_2 | ~spl2_5),
% 2.01/0.62    inference(avatar_contradiction_clause,[],[f413])).
% 2.01/0.62  fof(f413,plain,(
% 2.01/0.62    $false | (spl2_2 | ~spl2_5)),
% 2.01/0.62    inference(unit_resulting_resolution,[],[f23,f204,f321,f52,f119,f180])).
% 2.01/0.62  fof(f180,plain,(
% 2.01/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X2,k1_relat_1(X1)) | r1_tarski(X2,k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r1_tarski(X1,X0)) )),
% 2.01/0.62    inference(superposition,[],[f150,f58])).
% 2.01/0.62  fof(f58,plain,(
% 2.01/0.62    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X1,X1,X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 2.01/0.62    inference(superposition,[],[f49,f47])).
% 2.01/0.62  fof(f47,plain,(
% 2.01/0.62    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 2.01/0.62    inference(definition_unfolding,[],[f28,f42,f42])).
% 2.01/0.62  fof(f42,plain,(
% 2.01/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.01/0.62    inference(definition_unfolding,[],[f30,f39])).
% 2.01/0.62  fof(f39,plain,(
% 2.01/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.01/0.62    inference(cnf_transformation,[],[f8])).
% 2.01/0.62  fof(f8,axiom,(
% 2.01/0.62    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.01/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.01/0.62  fof(f30,plain,(
% 2.01/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.01/0.62    inference(cnf_transformation,[],[f7])).
% 2.01/0.62  fof(f7,axiom,(
% 2.01/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.01/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.01/0.62  fof(f28,plain,(
% 2.01/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.01/0.62    inference(cnf_transformation,[],[f6])).
% 2.01/0.62  fof(f6,axiom,(
% 2.01/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.01/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.01/0.62  fof(f49,plain,(
% 2.01/0.62    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 2.01/0.62    inference(definition_unfolding,[],[f33,f43])).
% 2.01/0.62  fof(f43,plain,(
% 2.01/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 2.01/0.62    inference(definition_unfolding,[],[f31,f42])).
% 2.01/0.62  fof(f31,plain,(
% 2.01/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.01/0.62    inference(cnf_transformation,[],[f9])).
% 2.01/0.62  fof(f9,axiom,(
% 2.01/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.01/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.01/0.62  fof(f33,plain,(
% 2.01/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.01/0.62    inference(cnf_transformation,[],[f19])).
% 2.01/0.62  fof(f19,plain,(
% 2.01/0.62    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.01/0.62    inference(ennf_transformation,[],[f3])).
% 2.01/0.62  fof(f3,axiom,(
% 2.01/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.01/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.01/0.62  fof(f150,plain,(
% 2.01/0.62    ( ! [X4,X2,X3] : (r1_tarski(X4,k1_relat_1(k3_tarski(k2_enumset1(X2,X2,X2,X3)))) | ~r1_tarski(X4,k1_relat_1(X3)) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 2.01/0.62    inference(superposition,[],[f50,f46])).
% 2.01/0.62  fof(f46,plain,(
% 2.01/0.62    ( ! [X0,X1] : (k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.01/0.62    inference(definition_unfolding,[],[f26,f43,f43])).
% 2.01/0.62  fof(f26,plain,(
% 2.01/0.62    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) )),
% 2.01/0.62    inference(cnf_transformation,[],[f17])).
% 2.01/0.62  fof(f17,plain,(
% 2.01/0.62    ! [X0] : (! [X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.01/0.62    inference(ennf_transformation,[],[f13])).
% 2.01/0.62  fof(f13,axiom,(
% 2.01/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))))),
% 2.01/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).
% 2.01/0.62  fof(f50,plain,(
% 2.01/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 2.01/0.62    inference(definition_unfolding,[],[f40,f43])).
% 2.01/0.62  fof(f40,plain,(
% 2.01/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 2.01/0.62    inference(cnf_transformation,[],[f20])).
% 2.01/0.62  fof(f20,plain,(
% 2.01/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.01/0.62    inference(ennf_transformation,[],[f2])).
% 2.01/0.62  fof(f2,axiom,(
% 2.01/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.01/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 2.01/0.62  fof(f119,plain,(
% 2.01/0.62    ~r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1)) | spl2_2),
% 2.01/0.62    inference(avatar_component_clause,[],[f117])).
% 2.01/0.62  fof(f117,plain,(
% 2.01/0.62    spl2_2 <=> r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1))),
% 2.01/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.01/0.62  fof(f52,plain,(
% 2.01/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.01/0.62    inference(equality_resolution,[],[f35])).
% 2.01/0.62  fof(f35,plain,(
% 2.01/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.01/0.62    inference(cnf_transformation,[],[f1])).
% 2.01/0.62  fof(f1,axiom,(
% 2.01/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.01/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.01/0.62  fof(f321,plain,(
% 2.01/0.62    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),X0)) )),
% 2.01/0.62    inference(superposition,[],[f295,f47])).
% 2.01/0.62  fof(f295,plain,(
% 2.01/0.62    ( ! [X4,X3] : (r1_tarski(k1_setfam_1(k2_enumset1(X3,X3,X3,X4)),X3)) )),
% 2.01/0.62    inference(resolution,[],[f253,f52])).
% 2.01/0.62  fof(f253,plain,(
% 2.01/0.62    ( ! [X4,X2,X3] : (~r1_tarski(X4,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) | r1_tarski(X4,X2)) )),
% 2.01/0.62    inference(superposition,[],[f50,f207])).
% 2.01/0.62  fof(f207,plain,(
% 2.01/0.62    ( ! [X0,X1] : (k3_tarski(k2_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) = X0) )),
% 2.01/0.62    inference(forward_demodulation,[],[f48,f47])).
% 2.01/0.62  fof(f48,plain,(
% 2.01/0.62    ( ! [X0,X1] : (k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k4_xboole_0(X0,X1))) = X0) )),
% 2.01/0.62    inference(definition_unfolding,[],[f32,f43,f44])).
% 2.01/0.62  fof(f44,plain,(
% 2.01/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 2.01/0.62    inference(definition_unfolding,[],[f29,f42])).
% 2.01/0.62  fof(f29,plain,(
% 2.01/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.01/0.62    inference(cnf_transformation,[],[f10])).
% 2.01/0.62  fof(f10,axiom,(
% 2.01/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.01/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.01/0.62  fof(f32,plain,(
% 2.01/0.62    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.01/0.62    inference(cnf_transformation,[],[f5])).
% 2.01/0.62  fof(f5,axiom,(
% 2.01/0.62    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.01/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 2.01/0.62  fof(f204,plain,(
% 2.01/0.62    v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | ~spl2_5),
% 2.01/0.62    inference(avatar_component_clause,[],[f203])).
% 2.01/0.62  fof(f203,plain,(
% 2.01/0.62    spl2_5 <=> v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 2.01/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 2.01/0.62  fof(f23,plain,(
% 2.01/0.62    v1_relat_1(sK1)),
% 2.01/0.62    inference(cnf_transformation,[],[f16])).
% 2.01/0.62  fof(f16,plain,(
% 2.01/0.62    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.01/0.62    inference(ennf_transformation,[],[f15])).
% 2.01/0.62  fof(f15,negated_conjecture,(
% 2.01/0.62    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 2.01/0.62    inference(negated_conjecture,[],[f14])).
% 2.01/0.62  fof(f14,conjecture,(
% 2.01/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 2.01/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).
% 2.01/0.62  fof(f328,plain,(
% 2.01/0.62    spl2_5),
% 2.01/0.62    inference(avatar_contradiction_clause,[],[f309])).
% 2.01/0.62  fof(f309,plain,(
% 2.01/0.62    $false | spl2_5),
% 2.01/0.62    inference(unit_resulting_resolution,[],[f25,f52,f52,f205,f295,f139])).
% 2.01/0.62  fof(f139,plain,(
% 2.01/0.62    ( ! [X6,X4,X7,X5] : (~r1_tarski(X7,X4) | ~v1_relat_1(X6) | v1_relat_1(X7) | ~r1_tarski(X5,X6) | ~r1_tarski(X4,X5)) )),
% 2.01/0.62    inference(superposition,[],[f90,f49])).
% 2.01/0.62  fof(f90,plain,(
% 2.01/0.62    ( ! [X4,X2,X5,X3] : (~r1_tarski(k3_tarski(k2_enumset1(X4,X4,X4,X5)),X3) | ~v1_relat_1(X3) | v1_relat_1(X2) | ~r1_tarski(X2,X4)) )),
% 2.01/0.62    inference(resolution,[],[f86,f62])).
% 2.01/0.62  fof(f62,plain,(
% 2.01/0.62    ( ! [X2,X0,X1] : (r1_tarski(X2,k3_tarski(k2_enumset1(X1,X1,X1,X0))) | ~r1_tarski(X2,X1)) )),
% 2.01/0.62    inference(superposition,[],[f50,f47])).
% 2.01/0.62  fof(f86,plain,(
% 2.01/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | v1_relat_1(X2) | ~v1_relat_1(X0) | ~r1_tarski(X1,X0)) )),
% 2.01/0.62    inference(superposition,[],[f61,f58])).
% 2.01/0.62  fof(f61,plain,(
% 2.01/0.62    ( ! [X4,X5,X3] : (~v1_relat_1(k3_tarski(k2_enumset1(X5,X5,X5,X4))) | v1_relat_1(X3) | ~r1_tarski(X3,X4)) )),
% 2.01/0.62    inference(resolution,[],[f50,f55])).
% 2.01/0.62  fof(f55,plain,(
% 2.01/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.01/0.62    inference(resolution,[],[f27,f37])).
% 2.01/0.62  fof(f37,plain,(
% 2.01/0.62    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.01/0.62    inference(cnf_transformation,[],[f11])).
% 2.01/0.62  fof(f11,axiom,(
% 2.01/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.01/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.01/0.62  fof(f27,plain,(
% 2.01/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 2.01/0.62    inference(cnf_transformation,[],[f18])).
% 2.01/0.62  fof(f18,plain,(
% 2.01/0.62    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.01/0.62    inference(ennf_transformation,[],[f12])).
% 2.01/0.62  fof(f12,axiom,(
% 2.01/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.01/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.01/0.62  fof(f205,plain,(
% 2.01/0.62    ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | spl2_5),
% 2.01/0.62    inference(avatar_component_clause,[],[f203])).
% 2.01/0.62  fof(f25,plain,(
% 2.01/0.62    v1_relat_1(sK0)),
% 2.01/0.62    inference(cnf_transformation,[],[f16])).
% 2.01/0.62  fof(f303,plain,(
% 2.01/0.62    spl2_4),
% 2.01/0.62    inference(avatar_contradiction_clause,[],[f302])).
% 2.01/0.62  fof(f302,plain,(
% 2.01/0.62    $false | spl2_4),
% 2.01/0.62    inference(subsumption_resolution,[],[f25,f201])).
% 2.01/0.62  fof(f201,plain,(
% 2.01/0.62    ~v1_relat_1(sK0) | spl2_4),
% 2.01/0.62    inference(avatar_component_clause,[],[f199])).
% 2.01/0.62  fof(f199,plain,(
% 2.01/0.62    spl2_4 <=> v1_relat_1(sK0)),
% 2.01/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.01/0.62  fof(f301,plain,(
% 2.01/0.62    spl2_3),
% 2.01/0.62    inference(avatar_contradiction_clause,[],[f293])).
% 2.01/0.62  fof(f293,plain,(
% 2.01/0.62    $false | spl2_3),
% 2.01/0.62    inference(unit_resulting_resolution,[],[f197,f52,f253])).
% 2.01/0.62  fof(f197,plain,(
% 2.01/0.62    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) | spl2_3),
% 2.01/0.62    inference(avatar_component_clause,[],[f195])).
% 2.01/0.62  fof(f195,plain,(
% 2.01/0.62    spl2_3 <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0)),
% 2.01/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.01/0.62  fof(f206,plain,(
% 2.01/0.62    ~spl2_3 | ~spl2_4 | ~spl2_5 | spl2_1),
% 2.01/0.62    inference(avatar_split_clause,[],[f185,f113,f203,f199,f195])).
% 2.01/0.62  fof(f113,plain,(
% 2.01/0.62    spl2_1 <=> r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0))),
% 2.01/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.01/0.62  fof(f185,plain,(
% 2.01/0.62    ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | ~v1_relat_1(sK0) | ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) | spl2_1),
% 2.01/0.62    inference(resolution,[],[f184,f115])).
% 2.01/0.62  fof(f115,plain,(
% 2.01/0.62    ~r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0)) | spl2_1),
% 2.01/0.62    inference(avatar_component_clause,[],[f113])).
% 2.01/0.62  fof(f184,plain,(
% 2.01/0.62    ( ! [X4,X5] : (r1_tarski(k1_relat_1(X4),k1_relat_1(X5)) | ~v1_relat_1(X4) | ~v1_relat_1(X5) | ~r1_tarski(X4,X5)) )),
% 2.01/0.62    inference(resolution,[],[f180,f52])).
% 2.01/0.62  fof(f120,plain,(
% 2.01/0.62    ~spl2_1 | ~spl2_2),
% 2.01/0.62    inference(avatar_split_clause,[],[f111,f117,f113])).
% 2.01/0.62  fof(f111,plain,(
% 2.01/0.62    ~r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0))),
% 2.01/0.62    inference(resolution,[],[f45,f51])).
% 2.01/0.62  fof(f51,plain,(
% 2.01/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.01/0.62    inference(definition_unfolding,[],[f41,f44])).
% 2.01/0.62  fof(f41,plain,(
% 2.01/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 2.01/0.62    inference(cnf_transformation,[],[f22])).
% 2.01/0.62  fof(f22,plain,(
% 2.01/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 2.01/0.62    inference(flattening,[],[f21])).
% 2.01/0.62  fof(f21,plain,(
% 2.01/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.01/0.62    inference(ennf_transformation,[],[f4])).
% 2.01/0.62  fof(f4,axiom,(
% 2.01/0.62    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 2.01/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 2.01/0.62  fof(f45,plain,(
% 2.01/0.62    ~r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))))),
% 2.01/0.62    inference(definition_unfolding,[],[f24,f44,f44])).
% 2.01/0.62  fof(f24,plain,(
% 2.01/0.62    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),
% 2.01/0.62    inference(cnf_transformation,[],[f16])).
% 2.01/0.62  % SZS output end Proof for theBenchmark
% 2.01/0.62  % (25787)------------------------------
% 2.01/0.62  % (25787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.62  % (25787)Termination reason: Refutation
% 2.01/0.62  
% 2.01/0.62  % (25787)Memory used [KB]: 6908
% 2.01/0.62  % (25787)Time elapsed: 0.198 s
% 2.01/0.62  % (25787)------------------------------
% 2.01/0.62  % (25787)------------------------------
% 2.01/0.62  % (25770)Success in time 0.26 s
%------------------------------------------------------------------------------
