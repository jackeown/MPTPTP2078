%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 473 expanded)
%              Number of leaves         :   24 ( 160 expanded)
%              Depth                    :   15
%              Number of atoms          :  241 ( 724 expanded)
%              Number of equality atoms :   31 ( 323 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f936,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f159,f233,f238,f245,f262,f280,f296,f375,f510,f625,f935])).

fof(f935,plain,(
    spl3_11 ),
    inference(avatar_contradiction_clause,[],[f934])).

fof(f934,plain,
    ( $false
    | spl3_11 ),
    inference(resolution,[],[f893,f30])).

fof(f30,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

fof(f893,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_11 ),
    inference(resolution,[],[f874,f279])).

fof(f279,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK1))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl3_11
  <=> r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f874,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(k7_relat_1(X0,X1),X2),k7_relat_1(X0,X2))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f857])).

fof(f857,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(k7_relat_1(X0,X1),X2),k7_relat_1(X0,X2))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f202,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f53,f52])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f39,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f45,f49])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f202,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k7_relat_1(X8,k4_xboole_0(X7,k4_xboole_0(X7,X6))),k7_relat_1(X8,X6))
      | ~ v1_relat_1(X8) ) ),
    inference(forward_demodulation,[],[f195,f52])).

fof(f195,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k7_relat_1(X8,k1_setfam_1(k2_enumset1(X7,X7,X7,X6))),k7_relat_1(X8,X6))
      | ~ v1_relat_1(X8) ) ),
    inference(superposition,[],[f175,f63])).

fof(f63,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k1_setfam_1(k2_enumset1(X5,X5,X5,X4)) ),
    inference(superposition,[],[f51,f52])).

fof(f51,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f36,f49,f49])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f175,plain,(
    ! [X28,X26,X27] :
      ( r1_tarski(k7_relat_1(X26,k4_xboole_0(X27,k4_xboole_0(X27,X28))),k7_relat_1(X26,X27))
      | ~ v1_relat_1(X26) ) ),
    inference(superposition,[],[f35,f161])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k7_relat_1(X2,X0),k4_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f160,f52])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k4_xboole_0(k7_relat_1(X2,X0),k4_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f54,f52])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k1_setfam_1(k2_enumset1(k7_relat_1(X2,X0),k7_relat_1(X2,X0),k7_relat_1(X2,X0),k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f46,f49,f49])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_relat_1)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f625,plain,(
    spl3_12 ),
    inference(avatar_contradiction_clause,[],[f624])).

fof(f624,plain,
    ( $false
    | spl3_12 ),
    inference(resolution,[],[f623,f30])).

fof(f623,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_12 ),
    inference(resolution,[],[f509,f200])).

fof(f200,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(k7_relat_1(X0,X1),X2),k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f197])).

fof(f197,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(k7_relat_1(X0,X1),X2),k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f175,f92])).

fof(f509,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK0))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f507])).

fof(f507,plain,
    ( spl3_12
  <=> r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f510,plain,
    ( ~ spl3_3
    | ~ spl3_9
    | ~ spl3_7
    | ~ spl3_12
    | spl3_5 ),
    inference(avatar_split_clause,[],[f504,f235,f507,f248,f269,f226])).

fof(f226,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f269,plain,
    ( spl3_9
  <=> v1_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f248,plain,
    ( spl3_7
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f235,plain,
    ( spl3_5
  <=> r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f504,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1))
    | ~ v1_relat_1(sK2)
    | spl3_5 ),
    inference(resolution,[],[f237,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_relat_1(X2),k9_relat_1(X0,X1))
      | ~ r1_tarski(X2,k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f33,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f237,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK0))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f235])).

fof(f375,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f374])).

fof(f374,plain,
    ( $false
    | spl3_9 ),
    inference(resolution,[],[f372,f30])).

fof(f372,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_9 ),
    inference(resolution,[],[f271,f121])).

fof(f121,plain,(
    ! [X4,X5,X3] :
      ( v1_relat_1(k7_relat_1(k7_relat_1(X3,X4),X5))
      | ~ v1_relat_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,(
    ! [X4,X5,X3] :
      ( v1_relat_1(k7_relat_1(k7_relat_1(X3,X4),X5))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f40,f92])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f271,plain,
    ( ~ v1_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f269])).

fof(f296,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | spl3_10 ),
    inference(resolution,[],[f281,f30])).

fof(f281,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_10 ),
    inference(resolution,[],[f275,f40])).

fof(f275,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl3_10
  <=> v1_relat_1(k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f280,plain,
    ( ~ spl3_3
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | spl3_4 ),
    inference(avatar_split_clause,[],[f263,f230,f277,f273,f269,f226])).

fof(f230,plain,
    ( spl3_4
  <=> r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f263,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1))
    | ~ v1_relat_1(sK2)
    | spl3_4 ),
    inference(resolution,[],[f62,f232])).

fof(f232,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK1))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f230])).

fof(f262,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | spl3_7 ),
    inference(resolution,[],[f260,f30])).

fof(f260,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_7 ),
    inference(resolution,[],[f250,f40])).

fof(f250,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f248])).

fof(f245,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f228,f30])).

fof(f228,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f226])).

fof(f238,plain,
    ( ~ spl3_3
    | ~ spl3_5
    | spl3_1 ),
    inference(avatar_split_clause,[],[f221,f152,f235,f226])).

fof(f152,plain,
    ( spl3_1
  <=> r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f221,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(superposition,[],[f154,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k2_relat_1(k7_relat_1(k7_relat_1(X0,X1),X2))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k2_relat_1(k7_relat_1(k7_relat_1(X0,X1),X2))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f41,f92])).

fof(f154,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f152])).

fof(f233,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_2 ),
    inference(avatar_split_clause,[],[f220,f156,f230,f226])).

fof(f156,plain,
    ( spl3_2
  <=> r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f220,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | spl3_2 ),
    inference(superposition,[],[f158,f122])).

fof(f158,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f156])).

fof(f159,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f150,f156,f152])).

fof(f150,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK1))
    | ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f133,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f55,f52])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f49])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f133,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
    inference(forward_demodulation,[],[f132,f52])).

fof(f132,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
    inference(forward_demodulation,[],[f50,f52])).

fof(f50,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
    inference(definition_unfolding,[],[f31,f49,f49])).

fof(f31,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:46:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.47  % (5762)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (5769)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.50  % (5755)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.51  % (5756)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.51  % (5758)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.51  % (5771)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (5754)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.52  % (5757)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (5761)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.52  % (5767)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.52  % (5760)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (5763)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.52  % (5764)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.53  % (5765)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.53  % (5768)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.53  % (5753)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.53  % (5766)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.56  % (5770)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.57  % (5757)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f936,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(avatar_sat_refutation,[],[f159,f233,f238,f245,f262,f280,f296,f375,f510,f625,f935])).
% 0.22/0.58  fof(f935,plain,(
% 0.22/0.58    spl3_11),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f934])).
% 0.22/0.58  fof(f934,plain,(
% 0.22/0.58    $false | spl3_11),
% 0.22/0.58    inference(resolution,[],[f893,f30])).
% 0.22/0.58  fof(f30,plain,(
% 0.22/0.58    v1_relat_1(sK2)),
% 0.22/0.58    inference(cnf_transformation,[],[f28])).
% 0.22/0.58  fof(f28,plain,(
% 0.22/0.58    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2)),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f27])).
% 0.22/0.58  fof(f27,plain,(
% 0.22/0.58    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f17,plain,(
% 0.22/0.58    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2))),
% 0.22/0.58    inference(ennf_transformation,[],[f16])).
% 0.22/0.58  fof(f16,negated_conjecture,(
% 0.22/0.58    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.22/0.58    inference(negated_conjecture,[],[f15])).
% 0.22/0.58  fof(f15,conjecture,(
% 0.22/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).
% 0.22/0.58  fof(f893,plain,(
% 0.22/0.58    ~v1_relat_1(sK2) | spl3_11),
% 0.22/0.58    inference(resolution,[],[f874,f279])).
% 0.22/0.58  fof(f279,plain,(
% 0.22/0.58    ~r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK1)) | spl3_11),
% 0.22/0.58    inference(avatar_component_clause,[],[f277])).
% 0.22/0.58  fof(f277,plain,(
% 0.22/0.58    spl3_11 <=> r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK1))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.58  fof(f874,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(k7_relat_1(X0,X1),X2),k7_relat_1(X0,X2)) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f857])).
% 0.22/0.58  fof(f857,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(k7_relat_1(X0,X1),X2),k7_relat_1(X0,X2)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(superposition,[],[f202,f92])).
% 0.22/0.58  fof(f92,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~v1_relat_1(X2)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f53,f52])).
% 0.22/0.58  fof(f52,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.22/0.58    inference(definition_unfolding,[],[f39,f49])).
% 0.22/0.58  fof(f49,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.22/0.58    inference(definition_unfolding,[],[f37,f48])).
% 0.22/0.58  fof(f48,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.58    inference(definition_unfolding,[],[f38,f44])).
% 0.22/0.58  fof(f44,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f6])).
% 0.22/0.58  fof(f6,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.58  fof(f38,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f5])).
% 0.22/0.58  fof(f5,axiom,(
% 0.22/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.58  fof(f37,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f7])).
% 0.22/0.58  fof(f7,axiom,(
% 0.22/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.58  fof(f39,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f4])).
% 0.22/0.58  fof(f4,axiom,(
% 0.22/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.58  fof(f53,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 0.22/0.58    inference(definition_unfolding,[],[f45,f49])).
% 0.22/0.58  fof(f45,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f23])).
% 0.22/0.58  fof(f23,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.58    inference(ennf_transformation,[],[f11])).
% 0.22/0.58  fof(f11,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 0.22/0.58  fof(f202,plain,(
% 0.22/0.58    ( ! [X6,X8,X7] : (r1_tarski(k7_relat_1(X8,k4_xboole_0(X7,k4_xboole_0(X7,X6))),k7_relat_1(X8,X6)) | ~v1_relat_1(X8)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f195,f52])).
% 0.22/0.58  fof(f195,plain,(
% 0.22/0.58    ( ! [X6,X8,X7] : (r1_tarski(k7_relat_1(X8,k1_setfam_1(k2_enumset1(X7,X7,X7,X6))),k7_relat_1(X8,X6)) | ~v1_relat_1(X8)) )),
% 0.22/0.58    inference(superposition,[],[f175,f63])).
% 0.22/0.58  fof(f63,plain,(
% 0.22/0.58    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k1_setfam_1(k2_enumset1(X5,X5,X5,X4))) )),
% 0.22/0.58    inference(superposition,[],[f51,f52])).
% 0.22/0.58  fof(f51,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) )),
% 0.22/0.58    inference(definition_unfolding,[],[f36,f49,f49])).
% 0.22/0.58  fof(f36,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f1])).
% 0.22/0.58  fof(f1,axiom,(
% 0.22/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.58  fof(f175,plain,(
% 0.22/0.58    ( ! [X28,X26,X27] : (r1_tarski(k7_relat_1(X26,k4_xboole_0(X27,k4_xboole_0(X27,X28))),k7_relat_1(X26,X27)) | ~v1_relat_1(X26)) )),
% 0.22/0.58    inference(superposition,[],[f35,f161])).
% 0.22/0.58  fof(f161,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k7_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k7_relat_1(X2,X0),k4_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f160,f52])).
% 0.22/0.58  fof(f160,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k4_xboole_0(k7_relat_1(X2,X0),k4_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f54,f52])).
% 0.22/0.58  fof(f54,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k1_setfam_1(k2_enumset1(k7_relat_1(X2,X0),k7_relat_1(X2,X0),k7_relat_1(X2,X0),k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 0.22/0.58    inference(definition_unfolding,[],[f46,f49,f49])).
% 0.22/0.58  fof(f46,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f24])).
% 0.22/0.58  fof(f24,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.22/0.58    inference(ennf_transformation,[],[f12])).
% 0.22/0.58  fof(f12,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_relat_1)).
% 0.22/0.58  fof(f35,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f3])).
% 0.22/0.58  fof(f3,axiom,(
% 0.22/0.58    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.58  fof(f625,plain,(
% 0.22/0.58    spl3_12),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f624])).
% 0.22/0.58  fof(f624,plain,(
% 0.22/0.58    $false | spl3_12),
% 0.22/0.58    inference(resolution,[],[f623,f30])).
% 0.22/0.58  fof(f623,plain,(
% 0.22/0.58    ~v1_relat_1(sK2) | spl3_12),
% 0.22/0.58    inference(resolution,[],[f509,f200])).
% 0.22/0.58  fof(f200,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(k7_relat_1(X0,X1),X2),k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f197])).
% 0.22/0.58  fof(f197,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(k7_relat_1(X0,X1),X2),k7_relat_1(X0,X1)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(superposition,[],[f175,f92])).
% 0.22/0.58  fof(f509,plain,(
% 0.22/0.58    ~r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK0)) | spl3_12),
% 0.22/0.58    inference(avatar_component_clause,[],[f507])).
% 0.22/0.58  fof(f507,plain,(
% 0.22/0.58    spl3_12 <=> r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.58  fof(f510,plain,(
% 0.22/0.58    ~spl3_3 | ~spl3_9 | ~spl3_7 | ~spl3_12 | spl3_5),
% 0.22/0.58    inference(avatar_split_clause,[],[f504,f235,f507,f248,f269,f226])).
% 0.22/0.58  fof(f226,plain,(
% 0.22/0.58    spl3_3 <=> v1_relat_1(sK2)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.58  fof(f269,plain,(
% 0.22/0.58    spl3_9 <=> v1_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.58  fof(f248,plain,(
% 0.22/0.58    spl3_7 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.58  fof(f235,plain,(
% 0.22/0.58    spl3_5 <=> r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.58  fof(f504,plain,(
% 0.22/0.58    ~r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)) | ~v1_relat_1(sK2) | spl3_5),
% 0.22/0.58    inference(resolution,[],[f237,f62])).
% 0.22/0.58  fof(f62,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(X2),k9_relat_1(X0,X1)) | ~r1_tarski(X2,k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(superposition,[],[f33,f41])).
% 0.22/0.58  fof(f41,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f22])).
% 0.22/0.58  fof(f22,plain,(
% 0.22/0.58    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.58    inference(ennf_transformation,[],[f13])).
% 0.22/0.58  fof(f13,axiom,(
% 0.22/0.58    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.58  fof(f33,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f19])).
% 0.22/0.58  fof(f19,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.58    inference(flattening,[],[f18])).
% 0.22/0.58  fof(f18,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f14])).
% 0.22/0.58  fof(f14,axiom,(
% 0.22/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.22/0.58  fof(f237,plain,(
% 0.22/0.58    ~r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK0)) | spl3_5),
% 0.22/0.58    inference(avatar_component_clause,[],[f235])).
% 0.22/0.58  fof(f375,plain,(
% 0.22/0.58    spl3_9),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f374])).
% 0.22/0.58  fof(f374,plain,(
% 0.22/0.58    $false | spl3_9),
% 0.22/0.58    inference(resolution,[],[f372,f30])).
% 0.22/0.58  fof(f372,plain,(
% 0.22/0.58    ~v1_relat_1(sK2) | spl3_9),
% 0.22/0.58    inference(resolution,[],[f271,f121])).
% 0.22/0.58  fof(f121,plain,(
% 0.22/0.58    ( ! [X4,X5,X3] : (v1_relat_1(k7_relat_1(k7_relat_1(X3,X4),X5)) | ~v1_relat_1(X3)) )),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f120])).
% 0.22/0.58  fof(f120,plain,(
% 0.22/0.58    ( ! [X4,X5,X3] : (v1_relat_1(k7_relat_1(k7_relat_1(X3,X4),X5)) | ~v1_relat_1(X3) | ~v1_relat_1(X3)) )),
% 0.22/0.58    inference(superposition,[],[f40,f92])).
% 0.22/0.58  fof(f40,plain,(
% 0.22/0.58    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f21])).
% 0.22/0.58  fof(f21,plain,(
% 0.22/0.58    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f10])).
% 0.22/0.58  fof(f10,axiom,(
% 0.22/0.58    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.58  fof(f271,plain,(
% 0.22/0.58    ~v1_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)) | spl3_9),
% 0.22/0.58    inference(avatar_component_clause,[],[f269])).
% 0.22/0.58  fof(f296,plain,(
% 0.22/0.58    spl3_10),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f295])).
% 0.22/0.58  fof(f295,plain,(
% 0.22/0.58    $false | spl3_10),
% 0.22/0.58    inference(resolution,[],[f281,f30])).
% 0.22/0.58  fof(f281,plain,(
% 0.22/0.58    ~v1_relat_1(sK2) | spl3_10),
% 0.22/0.58    inference(resolution,[],[f275,f40])).
% 0.22/0.58  fof(f275,plain,(
% 0.22/0.58    ~v1_relat_1(k7_relat_1(sK2,sK1)) | spl3_10),
% 0.22/0.58    inference(avatar_component_clause,[],[f273])).
% 0.22/0.58  fof(f273,plain,(
% 0.22/0.58    spl3_10 <=> v1_relat_1(k7_relat_1(sK2,sK1))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.58  fof(f280,plain,(
% 0.22/0.58    ~spl3_3 | ~spl3_9 | ~spl3_10 | ~spl3_11 | spl3_4),
% 0.22/0.58    inference(avatar_split_clause,[],[f263,f230,f277,f273,f269,f226])).
% 0.22/0.58  fof(f230,plain,(
% 0.22/0.58    spl3_4 <=> r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK1))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.58  fof(f263,plain,(
% 0.22/0.58    ~r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK1)) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | ~v1_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)) | ~v1_relat_1(sK2) | spl3_4),
% 0.22/0.58    inference(resolution,[],[f62,f232])).
% 0.22/0.58  fof(f232,plain,(
% 0.22/0.58    ~r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK1)) | spl3_4),
% 0.22/0.58    inference(avatar_component_clause,[],[f230])).
% 0.22/0.58  fof(f262,plain,(
% 0.22/0.58    spl3_7),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f261])).
% 0.22/0.58  fof(f261,plain,(
% 0.22/0.58    $false | spl3_7),
% 0.22/0.58    inference(resolution,[],[f260,f30])).
% 0.22/0.58  fof(f260,plain,(
% 0.22/0.58    ~v1_relat_1(sK2) | spl3_7),
% 0.22/0.58    inference(resolution,[],[f250,f40])).
% 0.22/0.58  fof(f250,plain,(
% 0.22/0.58    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl3_7),
% 0.22/0.58    inference(avatar_component_clause,[],[f248])).
% 0.22/0.58  fof(f245,plain,(
% 0.22/0.58    spl3_3),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f244])).
% 0.22/0.58  fof(f244,plain,(
% 0.22/0.58    $false | spl3_3),
% 0.22/0.58    inference(resolution,[],[f228,f30])).
% 0.22/0.58  fof(f228,plain,(
% 0.22/0.58    ~v1_relat_1(sK2) | spl3_3),
% 0.22/0.58    inference(avatar_component_clause,[],[f226])).
% 0.22/0.58  fof(f238,plain,(
% 0.22/0.58    ~spl3_3 | ~spl3_5 | spl3_1),
% 0.22/0.58    inference(avatar_split_clause,[],[f221,f152,f235,f226])).
% 0.22/0.58  fof(f152,plain,(
% 0.22/0.58    spl3_1 <=> r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.58  fof(f221,plain,(
% 0.22/0.58    ~r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK0)) | ~v1_relat_1(sK2) | spl3_1),
% 0.22/0.58    inference(superposition,[],[f154,f122])).
% 0.22/0.58  fof(f122,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k9_relat_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k2_relat_1(k7_relat_1(k7_relat_1(X0,X1),X2)) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f119])).
% 0.22/0.58  fof(f119,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k9_relat_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k2_relat_1(k7_relat_1(k7_relat_1(X0,X1),X2)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.58    inference(superposition,[],[f41,f92])).
% 0.22/0.58  fof(f154,plain,(
% 0.22/0.58    ~r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK0)) | spl3_1),
% 0.22/0.58    inference(avatar_component_clause,[],[f152])).
% 0.22/0.58  fof(f233,plain,(
% 0.22/0.58    ~spl3_3 | ~spl3_4 | spl3_2),
% 0.22/0.58    inference(avatar_split_clause,[],[f220,f156,f230,f226])).
% 0.22/0.58  fof(f156,plain,(
% 0.22/0.58    spl3_2 <=> r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK1))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.58  fof(f220,plain,(
% 0.22/0.58    ~r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | spl3_2),
% 0.22/0.58    inference(superposition,[],[f158,f122])).
% 0.22/0.58  fof(f158,plain,(
% 0.22/0.58    ~r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK1)) | spl3_2),
% 0.22/0.58    inference(avatar_component_clause,[],[f156])).
% 0.22/0.58  fof(f159,plain,(
% 0.22/0.58    ~spl3_1 | ~spl3_2),
% 0.22/0.58    inference(avatar_split_clause,[],[f150,f156,f152])).
% 0.22/0.58  fof(f150,plain,(
% 0.22/0.58    ~r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK1)) | ~r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k9_relat_1(sK2,sK0))),
% 0.22/0.58    inference(resolution,[],[f133,f67])).
% 0.22/0.58  fof(f67,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f55,f52])).
% 0.22/0.58  fof(f55,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.58    inference(definition_unfolding,[],[f47,f49])).
% 0.22/0.58  fof(f47,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f26])).
% 0.22/0.58  fof(f26,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.58    inference(flattening,[],[f25])).
% 0.22/0.58  fof(f25,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.58    inference(ennf_transformation,[],[f2])).
% 0.22/0.58  fof(f2,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.22/0.58  fof(f133,plain,(
% 0.22/0.58    ~r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))),
% 0.22/0.58    inference(forward_demodulation,[],[f132,f52])).
% 0.22/0.58  fof(f132,plain,(
% 0.22/0.58    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))),
% 0.22/0.58    inference(forward_demodulation,[],[f50,f52])).
% 0.22/0.58  fof(f50,plain,(
% 0.22/0.58    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))),
% 0.22/0.58    inference(definition_unfolding,[],[f31,f49,f49])).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 0.22/0.58    inference(cnf_transformation,[],[f28])).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (5757)------------------------------
% 0.22/0.58  % (5757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (5757)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (5757)Memory used [KB]: 7164
% 0.22/0.58  % (5757)Time elapsed: 0.138 s
% 0.22/0.58  % (5757)------------------------------
% 0.22/0.58  % (5757)------------------------------
% 0.22/0.59  % (5751)Success in time 0.228 s
%------------------------------------------------------------------------------
