%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 243 expanded)
%              Number of leaves         :   22 (  92 expanded)
%              Depth                    :   10
%              Number of atoms          :  190 ( 481 expanded)
%              Number of equality atoms :   14 ( 121 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f177,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f119,f121,f124,f128,f130,f140,f174,f176])).

fof(f176,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl3_8 ),
    inference(resolution,[],[f139,f51])).

fof(f51,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2) ),
    inference(backward_demodulation,[],[f46,f43])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f33,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f46,plain,(
    ! [X2,X3] : r1_tarski(k1_setfam_1(k2_enumset1(X3,X3,X3,X2)),X2) ),
    inference(superposition,[],[f41,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f30,f38,f38])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f29,f39])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f139,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl3_8
  <=> r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f174,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | spl3_7 ),
    inference(resolution,[],[f135,f26])).

fof(f26,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

% (22331)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
fof(f23,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f22,f21,f20])).

fof(f20,plain,
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

% (22332)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
fof(f21,plain,
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

fof(f22,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

fof(f135,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl3_7
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f140,plain,
    ( ~ spl3_3
    | ~ spl3_7
    | ~ spl3_5
    | ~ spl3_8
    | spl3_2 ),
    inference(avatar_split_clause,[],[f131,f98,f137,f112,f133,f104])).

fof(f104,plain,
    ( spl3_3
  <=> v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f112,plain,
    ( spl3_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f98,plain,
    ( spl3_2
  <=> r1_xboole_0(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f131,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | spl3_2 ),
    inference(resolution,[],[f122,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

fof(f122,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k5_relat_1(sK0,sK2))
    | spl3_2 ),
    inference(resolution,[],[f100,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f100,plain,
    ( ~ r1_xboole_0(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f130,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f118,f53])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(backward_demodulation,[],[f41,f43])).

fof(f118,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl3_6
  <=> r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f128,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f125,f26])).

fof(f125,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(resolution,[],[f106,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f45,f43])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f44,f42])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f34,f39])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f106,plain,
    ( ~ v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f104])).

fof(f124,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f114,f24])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f114,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f112])).

fof(f121,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f110,f25])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f110,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl3_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f119,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_1 ),
    inference(avatar_split_clause,[],[f102,f94,f116,f112,f108,f104])).

fof(f94,plain,
    ( spl3_1
  <=> r1_tarski(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f102,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | spl3_1 ),
    inference(resolution,[],[f96,f28])).

fof(f96,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k5_relat_1(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f101,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f92,f98,f94])).

fof(f92,plain,
    ( ~ r1_xboole_0(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
    | ~ r1_tarski(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f83,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f83,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k5_relat_1(sK0,sK1),k4_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))) ),
    inference(forward_demodulation,[],[f82,f43])).

fof(f82,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k4_xboole_0(k5_relat_1(sK0,sK1),k4_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))) ),
    inference(forward_demodulation,[],[f40,f43])).

fof(f40,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k1_setfam_1(k2_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))) ),
    inference(definition_unfolding,[],[f27,f39,f39])).

fof(f27,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:49:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (22338)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % (22325)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (22335)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (22336)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (22336)Refutation not found, incomplete strategy% (22336)------------------------------
% 0.22/0.48  % (22336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (22334)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (22329)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (22336)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (22336)Memory used [KB]: 10618
% 0.22/0.48  % (22336)Time elapsed: 0.062 s
% 0.22/0.48  % (22336)------------------------------
% 0.22/0.48  % (22336)------------------------------
% 0.22/0.49  % (22339)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (22329)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f177,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f101,f119,f121,f124,f128,f130,f140,f174,f176])).
% 0.22/0.49  fof(f176,plain,(
% 0.22/0.49    spl3_8),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f175])).
% 0.22/0.49  fof(f175,plain,(
% 0.22/0.49    $false | spl3_8),
% 0.22/0.49    inference(resolution,[],[f139,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2)) )),
% 0.22/0.49    inference(backward_demodulation,[],[f46,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f33,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f32,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f31,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X2,X3] : (r1_tarski(k1_setfam_1(k2_enumset1(X3,X3,X3,X2)),X2)) )),
% 0.22/0.49    inference(superposition,[],[f41,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f30,f38,f38])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f29,f39])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) | spl3_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f137])).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    spl3_8 <=> r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.49  fof(f174,plain,(
% 0.22/0.49    spl3_7),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f173])).
% 0.22/0.49  fof(f173,plain,(
% 0.22/0.49    $false | spl3_7),
% 0.22/0.49    inference(resolution,[],[f135,f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    v1_relat_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  % (22331)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ((~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f22,f21,f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  % (22332)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,negated_conjecture,(
% 0.22/0.49    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 0.22/0.49    inference(negated_conjecture,[],[f11])).
% 0.22/0.49  fof(f11,conjecture,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | spl3_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f133])).
% 0.22/0.49  fof(f133,plain,(
% 0.22/0.49    spl3_7 <=> v1_relat_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.49  fof(f140,plain,(
% 0.22/0.49    ~spl3_3 | ~spl3_7 | ~spl3_5 | ~spl3_8 | spl3_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f131,f98,f137,f112,f133,f104])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    spl3_3 <=> v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    spl3_5 <=> v1_relat_1(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    spl3_2 <=> r1_xboole_0(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) | ~v1_relat_1(sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | spl3_2),
% 0.22/0.49    inference(resolution,[],[f122,f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).
% 0.22/0.49  fof(f122,plain,(
% 0.22/0.49    ~r1_tarski(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k5_relat_1(sK0,sK2)) | spl3_2),
% 0.22/0.49    inference(resolution,[],[f100,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    ~r1_xboole_0(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) | spl3_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f98])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    spl3_6),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f129])).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    $false | spl3_6),
% 0.22/0.49    inference(resolution,[],[f118,f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 0.22/0.49    inference(backward_demodulation,[],[f41,f43])).
% 0.22/0.49  fof(f118,plain,(
% 0.22/0.49    ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1) | spl3_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f116])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    spl3_6 <=> r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    spl3_3),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f127])).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    $false | spl3_3),
% 0.22/0.49    inference(resolution,[],[f125,f26])).
% 0.22/0.49  fof(f125,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | spl3_3),
% 0.22/0.49    inference(resolution,[],[f106,f56])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X0))) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f45,f43])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(superposition,[],[f44,f42])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f34,f39])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    ~v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | spl3_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f104])).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    spl3_5),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f123])).
% 0.22/0.49  fof(f123,plain,(
% 0.22/0.49    $false | spl3_5),
% 0.22/0.49    inference(resolution,[],[f114,f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    v1_relat_1(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    ~v1_relat_1(sK0) | spl3_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f112])).
% 0.22/0.49  fof(f121,plain,(
% 0.22/0.49    spl3_4),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f120])).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    $false | spl3_4),
% 0.22/0.49    inference(resolution,[],[f110,f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    v1_relat_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    ~v1_relat_1(sK1) | spl3_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f108])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    spl3_4 <=> v1_relat_1(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | spl3_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f102,f94,f116,f112,f108,f104])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    spl3_1 <=> r1_tarski(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k5_relat_1(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1) | ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | spl3_1),
% 0.22/0.49    inference(resolution,[],[f96,f28])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    ~r1_tarski(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k5_relat_1(sK0,sK1)) | spl3_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f94])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    ~spl3_1 | ~spl3_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f92,f98,f94])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    ~r1_xboole_0(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) | ~r1_tarski(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k5_relat_1(sK0,sK1))),
% 0.22/0.49    inference(resolution,[],[f83,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    ~r1_tarski(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k5_relat_1(sK0,sK1),k4_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))))),
% 0.22/0.49    inference(forward_demodulation,[],[f82,f43])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k4_xboole_0(k5_relat_1(sK0,sK1),k4_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))))),
% 0.22/0.49    inference(forward_demodulation,[],[f40,f43])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))),k1_setfam_1(k2_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))))),
% 0.22/0.49    inference(definition_unfolding,[],[f27,f39,f39])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (22329)------------------------------
% 0.22/0.49  % (22329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (22329)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (22329)Memory used [KB]: 6140
% 0.22/0.49  % (22329)Time elapsed: 0.066 s
% 0.22/0.49  % (22329)------------------------------
% 0.22/0.49  % (22329)------------------------------
% 0.22/0.49  % (22328)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (22324)Success in time 0.125 s
%------------------------------------------------------------------------------
