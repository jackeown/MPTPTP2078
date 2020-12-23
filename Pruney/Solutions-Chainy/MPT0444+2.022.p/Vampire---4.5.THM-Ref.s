%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 140 expanded)
%              Number of leaves         :   17 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  148 ( 293 expanded)
%              Number of equality atoms :    8 (  44 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f92,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f69,f71,f76,f85,f87,f89,f91])).

fof(f91,plain,(
    spl2_7 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | spl2_7 ),
    inference(resolution,[],[f84,f37])).

fof(f37,plain,(
    ! [X2,X3] : r1_tarski(k1_setfam_1(k1_enumset1(X3,X3,X2)),X2) ),
    inference(superposition,[],[f32,f33])).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f25,f26,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f24,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f84,plain,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK1)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl2_7
  <=> r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f89,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl2_5 ),
    inference(resolution,[],[f68,f32])).

fof(f68,plain,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl2_5
  <=> r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f87,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f86])).

fof(f86,plain,
    ( $false
    | spl2_6 ),
    inference(resolution,[],[f80,f20])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

fof(f80,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f85,plain,
    ( ~ spl2_3
    | ~ spl2_6
    | ~ spl2_7
    | spl2_2 ),
    inference(avatar_split_clause,[],[f74,f52,f82,f78,f58])).

fof(f58,plain,
    ( spl2_3
  <=> v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f52,plain,
    ( spl2_2
  <=> r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f74,plain,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))
    | spl2_2 ),
    inference(resolution,[],[f54,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f54,plain,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k2_relat_1(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f76,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f75])).

fof(f75,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f72,f20])).

fof(f72,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_3 ),
    inference(resolution,[],[f60,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f34,f33])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f28,f30])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f60,plain,
    ( ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f71,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f70])).

fof(f70,plain,
    ( $false
    | spl2_4 ),
    inference(resolution,[],[f64,f19])).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl2_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f69,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | spl2_1 ),
    inference(avatar_split_clause,[],[f56,f48,f66,f62,f58])).

fof(f48,plain,
    ( spl2_1
  <=> r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f56,plain,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))
    | spl2_1 ),
    inference(resolution,[],[f50,f23])).

fof(f50,plain,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k2_relat_1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f55,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f44,f52,f48])).

fof(f44,plain,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k2_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k2_relat_1(sK0)) ),
    inference(resolution,[],[f35,f31])).

fof(f31,plain,(
    ~ r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f21,f30,f30])).

fof(f21,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (5203)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.44  % (5203)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f92,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f55,f69,f71,f76,f85,f87,f89,f91])).
% 0.21/0.44  fof(f91,plain,(
% 0.21/0.44    spl2_7),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f90])).
% 0.21/0.44  fof(f90,plain,(
% 0.21/0.44    $false | spl2_7),
% 0.21/0.44    inference(resolution,[],[f84,f37])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ( ! [X2,X3] : (r1_tarski(k1_setfam_1(k1_enumset1(X3,X3,X2)),X2)) )),
% 0.21/0.44    inference(superposition,[],[f32,f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f25,f26,f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f24,f30])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f27,f26])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.44  fof(f84,plain,(
% 0.21/0.44    ~r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK1) | spl2_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f82])).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    spl2_7 <=> r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.45  fof(f89,plain,(
% 0.21/0.45    spl2_5),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f88])).
% 0.21/0.45  fof(f88,plain,(
% 0.21/0.45    $false | spl2_5),
% 0.21/0.45    inference(resolution,[],[f68,f32])).
% 0.21/0.45  fof(f68,plain,(
% 0.21/0.45    ~r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK0) | spl2_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f66])).
% 0.21/0.45  fof(f66,plain,(
% 0.21/0.45    spl2_5 <=> r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.45  fof(f87,plain,(
% 0.21/0.45    spl2_6),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f86])).
% 0.21/0.45  fof(f86,plain,(
% 0.21/0.45    $false | spl2_6),
% 0.21/0.45    inference(resolution,[],[f80,f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    v1_relat_1(sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f17,f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,negated_conjecture,(
% 0.21/0.45    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 0.21/0.45    inference(negated_conjecture,[],[f8])).
% 0.21/0.45  fof(f8,conjecture,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    ~v1_relat_1(sK1) | spl2_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f78])).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    spl2_6 <=> v1_relat_1(sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.45  fof(f85,plain,(
% 0.21/0.45    ~spl2_3 | ~spl2_6 | ~spl2_7 | spl2_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f74,f52,f82,f78,f58])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    spl2_3 <=> v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    spl2_2 <=> r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k2_relat_1(sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    ~r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) | spl2_2),
% 0.21/0.45    inference(resolution,[],[f54,f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(flattening,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ~r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k2_relat_1(sK1)) | spl2_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f52])).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    spl2_3),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f75])).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    $false | spl2_3),
% 0.21/0.45    inference(resolution,[],[f72,f20])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    ~v1_relat_1(sK1) | spl2_3),
% 0.21/0.45    inference(resolution,[],[f60,f36])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X0))) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(superposition,[],[f34,f33])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f28,f30])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    ~v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) | spl2_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f58])).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    spl2_4),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f70])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    $false | spl2_4),
% 0.21/0.45    inference(resolution,[],[f64,f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    v1_relat_1(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    ~v1_relat_1(sK0) | spl2_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f62])).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    spl2_4 <=> v1_relat_1(sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.45  fof(f69,plain,(
% 0.21/0.45    ~spl2_3 | ~spl2_4 | ~spl2_5 | spl2_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f56,f48,f66,f62,f58])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    spl2_1 <=> r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k2_relat_1(sK0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    ~r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) | spl2_1),
% 0.21/0.45    inference(resolution,[],[f50,f23])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    ~r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k2_relat_1(sK0)) | spl2_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f48])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    ~spl2_1 | ~spl2_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f44,f52,f48])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ~r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k2_relat_1(sK1)) | ~r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k2_relat_1(sK0))),
% 0.21/0.45    inference(resolution,[],[f35,f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ~r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1))))),
% 0.21/0.45    inference(definition_unfolding,[],[f21,f30,f30])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f29,f30])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.45    inference(flattening,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (5203)------------------------------
% 0.21/0.45  % (5203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (5203)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (5203)Memory used [KB]: 6140
% 0.21/0.45  % (5203)Time elapsed: 0.010 s
% 0.21/0.45  % (5203)------------------------------
% 0.21/0.45  % (5203)------------------------------
% 0.21/0.45  % (5195)Success in time 0.09 s
%------------------------------------------------------------------------------
