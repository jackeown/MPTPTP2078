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
% DateTime   : Thu Dec  3 12:54:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 274 expanded)
%              Number of leaves         :   24 (  95 expanded)
%              Depth                    :   13
%              Number of atoms          :  223 ( 475 expanded)
%              Number of equality atoms :   23 ( 150 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f294,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f140,f151,f157,f164,f172,f272,f275,f284,f289,f293])).

fof(f293,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f292])).

fof(f292,plain,
    ( $false
    | spl3_8 ),
    inference(resolution,[],[f291,f31])).

fof(f31,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_funct_1)).

fof(f291,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_8 ),
    inference(resolution,[],[f263,f118])).

fof(f118,plain,(
    ! [X21,X19,X20] :
      ( r1_tarski(k10_relat_1(k7_relat_1(X20,X19),X21),X19)
      | ~ v1_relat_1(X20) ) ),
    inference(superposition,[],[f35,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X2,X1)))
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
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,k10_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f45,f49])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f263,plain,
    ( ~ r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl3_8
  <=> r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f289,plain,(
    spl3_11 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | spl3_11 ),
    inference(resolution,[],[f283,f32])).

fof(f32,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f283,plain,
    ( ~ v1_funct_1(sK2)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl3_11
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f284,plain,
    ( ~ spl3_3
    | ~ spl3_11
    | spl3_10 ),
    inference(avatar_split_clause,[],[f279,f269,f281,f142])).

fof(f142,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f269,plain,
    ( spl3_10
  <=> v1_funct_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f279,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_10 ),
    inference(resolution,[],[f271,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f271,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,sK0))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f269])).

fof(f275,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f274])).

fof(f274,plain,
    ( $false
    | spl3_9 ),
    inference(resolution,[],[f273,f31])).

fof(f273,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_9 ),
    inference(resolution,[],[f267,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f267,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl3_9
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f272,plain,
    ( ~ spl3_3
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10
    | spl3_5 ),
    inference(avatar_split_clause,[],[f258,f154,f269,f265,f261,f142])).

fof(f154,plain,
    ( spl3_5
  <=> r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f258,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),sK0)
    | ~ v1_relat_1(sK2)
    | spl3_5 ),
    inference(resolution,[],[f59,f156])).

fof(f156,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f154])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X0,k10_relat_1(k7_relat_1(X0,X1),X2)),X2)
      | ~ v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ r1_tarski(k10_relat_1(k7_relat_1(X0,X1),X2),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f41,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f172,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f163,f35])).

fof(f163,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl3_6
  <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f164,plain,
    ( ~ spl3_3
    | ~ spl3_6
    | spl3_2 ),
    inference(avatar_split_clause,[],[f158,f137,f161,f142])).

fof(f137,plain,
    ( spl3_2
  <=> r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f158,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0)
    | ~ v1_relat_1(sK2)
    | spl3_2 ),
    inference(resolution,[],[f139,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

fof(f139,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f137])).

fof(f157,plain,
    ( ~ spl3_3
    | ~ spl3_5
    | spl3_1 ),
    inference(avatar_split_clause,[],[f152,f133,f154,f142])).

fof(f133,plain,
    ( spl3_1
  <=> r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f152,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1)
    | ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(superposition,[],[f135,f108])).

fof(f135,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f133])).

fof(f151,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f144,f31])).

fof(f144,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f142])).

fof(f140,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f130,f137,f133])).

fof(f130,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) ),
    inference(resolution,[],[f129,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f54,f52])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f129,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(sK1,k4_xboole_0(sK1,k9_relat_1(sK2,sK0)))) ),
    inference(forward_demodulation,[],[f128,f52])).

fof(f128,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(sK1,k4_xboole_0(sK1,k9_relat_1(sK2,sK0)))) ),
    inference(forward_demodulation,[],[f127,f52])).

fof(f127,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,k9_relat_1(sK2,sK0)))) ),
    inference(forward_demodulation,[],[f126,f55])).

fof(f55,plain,(
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

fof(f126,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1))) ),
    inference(forward_demodulation,[],[f50,f52])).

fof(f50,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
    inference(definition_unfolding,[],[f33,f49,f49])).

fof(f33,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:39:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (8744)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.45  % (8761)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.46  % (8756)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.46  % (8754)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.46  % (8746)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (8758)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.46  % (8748)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (8750)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (8748)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f294,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f140,f151,f157,f164,f172,f272,f275,f284,f289,f293])).
% 0.21/0.47  fof(f293,plain,(
% 0.21/0.47    spl3_8),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f292])).
% 0.21/0.47  fof(f292,plain,(
% 0.21/0.47    $false | spl3_8),
% 0.21/0.47    inference(resolution,[],[f291,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    v1_relat_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 0.21/0.47    inference(negated_conjecture,[],[f14])).
% 0.21/0.47  fof(f14,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_funct_1)).
% 0.21/0.47  fof(f291,plain,(
% 0.21/0.47    ~v1_relat_1(sK2) | spl3_8),
% 0.21/0.47    inference(resolution,[],[f263,f118])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    ( ! [X21,X19,X20] : (r1_tarski(k10_relat_1(k7_relat_1(X20,X19),X21),X19) | ~v1_relat_1(X20)) )),
% 0.21/0.47    inference(superposition,[],[f35,f108])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f53,f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f39,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f37,f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f38,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,k10_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f45,f49])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.47  fof(f263,plain,(
% 0.21/0.47    ~r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),sK0) | spl3_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f261])).
% 0.21/0.47  fof(f261,plain,(
% 0.21/0.47    spl3_8 <=> r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.47  fof(f289,plain,(
% 0.21/0.47    spl3_11),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f288])).
% 0.21/0.47  fof(f288,plain,(
% 0.21/0.47    $false | spl3_11),
% 0.21/0.47    inference(resolution,[],[f283,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    v1_funct_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f283,plain,(
% 0.21/0.47    ~v1_funct_1(sK2) | spl3_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f281])).
% 0.21/0.47  fof(f281,plain,(
% 0.21/0.47    spl3_11 <=> v1_funct_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.47  fof(f284,plain,(
% 0.21/0.47    ~spl3_3 | ~spl3_11 | spl3_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f279,f269,f281,f142])).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    spl3_3 <=> v1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f269,plain,(
% 0.21/0.47    spl3_10 <=> v1_funct_1(k7_relat_1(sK2,sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.47  fof(f279,plain,(
% 0.21/0.47    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_10),
% 0.21/0.47    inference(resolution,[],[f271,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).
% 0.21/0.47  fof(f271,plain,(
% 0.21/0.47    ~v1_funct_1(k7_relat_1(sK2,sK0)) | spl3_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f269])).
% 0.21/0.47  fof(f275,plain,(
% 0.21/0.47    spl3_9),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f274])).
% 0.21/0.47  fof(f274,plain,(
% 0.21/0.47    $false | spl3_9),
% 0.21/0.47    inference(resolution,[],[f273,f31])).
% 0.21/0.47  fof(f273,plain,(
% 0.21/0.47    ~v1_relat_1(sK2) | spl3_9),
% 0.21/0.47    inference(resolution,[],[f267,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.47  fof(f267,plain,(
% 0.21/0.47    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl3_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f265])).
% 0.21/0.47  fof(f265,plain,(
% 0.21/0.47    spl3_9 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.47  fof(f272,plain,(
% 0.21/0.47    ~spl3_3 | ~spl3_8 | ~spl3_9 | ~spl3_10 | spl3_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f258,f154,f269,f265,f261,f142])).
% 0.21/0.47  fof(f154,plain,(
% 0.21/0.47    spl3_5 <=> r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.47  fof(f258,plain,(
% 0.21/0.47    ~v1_funct_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),sK0) | ~v1_relat_1(sK2) | spl3_5),
% 0.21/0.47    inference(resolution,[],[f59,f156])).
% 0.21/0.47  fof(f156,plain,(
% 0.21/0.47    ~r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) | spl3_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f154])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X0,k10_relat_1(k7_relat_1(X0,X1),X2)),X2) | ~v1_funct_1(k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~r1_tarski(k10_relat_1(k7_relat_1(X0,X1),X2),X1) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(superposition,[],[f41,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 0.21/0.47  fof(f172,plain,(
% 0.21/0.47    spl3_6),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f170])).
% 0.21/0.47  fof(f170,plain,(
% 0.21/0.47    $false | spl3_6),
% 0.21/0.47    inference(resolution,[],[f163,f35])).
% 0.21/0.47  fof(f163,plain,(
% 0.21/0.47    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0) | spl3_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f161])).
% 0.21/0.47  fof(f161,plain,(
% 0.21/0.47    spl3_6 <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.47  fof(f164,plain,(
% 0.21/0.47    ~spl3_3 | ~spl3_6 | spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f158,f137,f161,f142])).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    spl3_2 <=> r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f158,plain,(
% 0.21/0.47    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0) | ~v1_relat_1(sK2) | spl3_2),
% 0.21/0.47    inference(resolution,[],[f139,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).
% 0.21/0.47  fof(f139,plain,(
% 0.21/0.47    ~r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) | spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f137])).
% 0.21/0.47  fof(f157,plain,(
% 0.21/0.47    ~spl3_3 | ~spl3_5 | spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f152,f133,f154,f142])).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    spl3_1 <=> r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    ~r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) | ~v1_relat_1(sK2) | spl3_1),
% 0.21/0.47    inference(superposition,[],[f135,f108])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    ~r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) | spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f133])).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    spl3_3),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f150])).
% 0.21/0.47  fof(f150,plain,(
% 0.21/0.47    $false | spl3_3),
% 0.21/0.47    inference(resolution,[],[f144,f31])).
% 0.21/0.47  fof(f144,plain,(
% 0.21/0.47    ~v1_relat_1(sK2) | spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f142])).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    ~spl3_1 | ~spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f130,f137,f133])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    ~r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) | ~r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1)),
% 0.21/0.47    inference(resolution,[],[f129,f74])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f54,f52])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f47,f49])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    ~r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(sK1,k4_xboole_0(sK1,k9_relat_1(sK2,sK0))))),
% 0.21/0.47    inference(forward_demodulation,[],[f128,f52])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(sK1,k4_xboole_0(sK1,k9_relat_1(sK2,sK0))))),
% 0.21/0.47    inference(forward_demodulation,[],[f127,f52])).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,k9_relat_1(sK2,sK0))))),
% 0.21/0.47    inference(forward_demodulation,[],[f126,f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k1_setfam_1(k2_enumset1(X5,X5,X5,X4))) )),
% 0.21/0.47    inference(superposition,[],[f51,f52])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f36,f49,f49])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1)))),
% 0.21/0.47    inference(forward_demodulation,[],[f50,f52])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)))),
% 0.21/0.47    inference(definition_unfolding,[],[f33,f49,f49])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (8748)------------------------------
% 0.21/0.47  % (8748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (8748)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (8748)Memory used [KB]: 6268
% 0.21/0.47  % (8748)Time elapsed: 0.058 s
% 0.21/0.47  % (8748)------------------------------
% 0.21/0.47  % (8748)------------------------------
% 0.21/0.47  % (8743)Success in time 0.112 s
%------------------------------------------------------------------------------
