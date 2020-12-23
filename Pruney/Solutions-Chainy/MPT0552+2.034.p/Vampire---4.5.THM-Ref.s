%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 438 expanded)
%              Number of leaves         :   26 ( 165 expanded)
%              Depth                    :   11
%              Number of atoms          :  300 ( 946 expanded)
%              Number of equality atoms :   31 ( 190 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f307,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f58,f81,f84,f88,f90,f104,f106,f125,f160,f162,f228,f232,f263,f264,f302,f306])).

fof(f306,plain,
    ( ~ spl3_2
    | spl3_14 ),
    inference(avatar_split_clause,[],[f305,f299,f47])).

fof(f47,plain,
    ( spl3_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f299,plain,
    ( spl3_14
  <=> v1_relat_1(k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f305,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_14 ),
    inference(resolution,[],[f301,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f301,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f299])).

fof(f302,plain,
    ( ~ spl3_14
    | ~ spl3_2
    | spl3_9 ),
    inference(avatar_split_clause,[],[f293,f122,f47,f299])).

fof(f122,plain,
    ( spl3_9
  <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f293,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ spl3_2
    | spl3_9 ),
    inference(resolution,[],[f222,f124])).

fof(f124,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK1))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f122])).

fof(f222,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X1,X1,X1,X0))),k9_relat_1(sK2,X0))
        | ~ v1_relat_1(k7_relat_1(sK2,X0)) )
    | ~ spl3_2 ),
    inference(superposition,[],[f180,f39])).

fof(f39,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f26,f36,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f180,plain,
    ( ! [X2,X1] :
        ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),k9_relat_1(sK2,X1))
        | ~ v1_relat_1(k7_relat_1(sK2,X1)) )
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f175,f51])).

fof(f51,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)
    | ~ spl3_2 ),
    inference(resolution,[],[f31,f49])).

fof(f49,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f175,plain,
    ( ! [X2,X1] :
        ( r1_tarski(k2_relat_1(k7_relat_1(sK2,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))),k9_relat_1(sK2,X1))
        | ~ v1_relat_1(k7_relat_1(sK2,X1)) )
    | ~ spl3_2 ),
    inference(superposition,[],[f54,f65])).

fof(f65,plain,
    ( ! [X0,X1] : k7_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k7_relat_1(sK2,X0),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
    | ~ spl3_2 ),
    inference(resolution,[],[f63,f38])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f25,f36])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X1),X0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f33,f49])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

fof(f54,plain,
    ( ! [X2,X1] :
        ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2)),k9_relat_1(sK2,X1))
        | ~ v1_relat_1(k7_relat_1(sK2,X1)) )
    | ~ spl3_2 ),
    inference(superposition,[],[f30,f51])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

fof(f264,plain,
    ( spl3_13
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f256,f118,f47,f260])).

fof(f260,plain,
    ( spl3_13
  <=> k7_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) = k7_relat_1(k7_relat_1(sK2,k9_relat_1(sK2,sK0)),k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f118,plain,
    ( spl3_8
  <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f256,plain,
    ( k7_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) = k7_relat_1(k7_relat_1(sK2,k9_relat_1(sK2,sK0)),k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))))
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(resolution,[],[f119,f63])).

fof(f119,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f263,plain,
    ( spl3_13
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f258,f118,f75,f56,f47,f260])).

fof(f56,plain,
    ( spl3_3
  <=> ! [X0] : r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f75,plain,
    ( spl3_4
  <=> v1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f258,plain,
    ( k7_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) = k7_relat_1(k7_relat_1(sK2,k9_relat_1(sK2,sK0)),k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f257,f69])).

fof(f69,plain,
    ( ! [X8] : k7_relat_1(sK2,k9_relat_1(sK2,X8)) = k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k9_relat_1(sK2,X8))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(resolution,[],[f63,f57])).

fof(f57,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f257,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k9_relat_1(sK2,sK0)),k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) = k7_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f255,f69])).

fof(f255,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k9_relat_1(sK2,sK0)),k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) = k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))))
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(resolution,[],[f119,f91])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k7_relat_1(k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),X1),X0) = k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),X0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f76,f33])).

fof(f76,plain,
    ( v1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f232,plain,
    ( ~ spl3_2
    | spl3_12 ),
    inference(avatar_split_clause,[],[f231,f225,f47])).

% (29740)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
fof(f225,plain,
    ( spl3_12
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f231,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_12 ),
    inference(resolution,[],[f227,f29])).

fof(f227,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f225])).

fof(f228,plain,
    ( ~ spl3_12
    | ~ spl3_2
    | spl3_8 ),
    inference(avatar_split_clause,[],[f219,f118,f47,f225])).

fof(f219,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ spl3_2
    | spl3_8 ),
    inference(resolution,[],[f180,f120])).

fof(f120,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK0))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f162,plain,
    ( ~ spl3_4
    | spl3_10 ),
    inference(avatar_split_clause,[],[f161,f154,f75])).

fof(f154,plain,
    ( spl3_10
  <=> v1_relat_1(k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f161,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)))
    | spl3_10 ),
    inference(resolution,[],[f156,f29])).

fof(f156,plain,
    ( ~ v1_relat_1(k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k2_relat_1(sK2)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f154])).

fof(f160,plain,
    ( ~ spl3_10
    | spl3_11
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f152,f75,f56,f47,f158,f154])).

fof(f158,plain,
    ( spl3_11
  <=> ! [X0] : r1_tarski(k9_relat_1(sK2,k9_relat_1(sK2,X0)),k9_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f152,plain,
    ( ! [X0] :
        ( r1_tarski(k9_relat_1(sK2,k9_relat_1(sK2,X0)),k9_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k2_relat_1(sK2)))
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k2_relat_1(sK2))) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f151,f51])).

fof(f151,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k7_relat_1(sK2,k9_relat_1(sK2,X0))),k9_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k2_relat_1(sK2)))
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k2_relat_1(sK2))) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f149,f92])).

fof(f92,plain,
    ( ! [X2] : k2_relat_1(k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),X2)) = k9_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),X2)
    | ~ spl3_4 ),
    inference(resolution,[],[f76,f31])).

fof(f149,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k7_relat_1(sK2,k9_relat_1(sK2,X0))),k2_relat_1(k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k2_relat_1(sK2))))
        | ~ v1_relat_1(k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k2_relat_1(sK2))) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(superposition,[],[f30,f144])).

fof(f144,plain,
    ( ! [X11] : k7_relat_1(k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k2_relat_1(sK2)),k9_relat_1(sK2,X11)) = k7_relat_1(sK2,k9_relat_1(sK2,X11))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f140,f69])).

fof(f140,plain,
    ( ! [X11] : k7_relat_1(k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k2_relat_1(sK2)),k9_relat_1(sK2,X11)) = k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k9_relat_1(sK2,X11))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(resolution,[],[f91,f57])).

fof(f125,plain,
    ( ~ spl3_8
    | ~ spl3_9
    | spl3_1 ),
    inference(avatar_split_clause,[],[f113,f42,f122,f118])).

fof(f42,plain,
    ( spl3_1
  <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f113,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK1))
    | ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK0))
    | spl3_1 ),
    inference(resolution,[],[f40,f44])).

fof(f44,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f106,plain,
    ( ~ spl3_4
    | spl3_7
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f105,f75,f47,f102,f75])).

fof(f102,plain,
    ( spl3_7
  <=> ! [X0] : r1_tarski(k9_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),X0),k9_relat_1(sK2,k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f105,plain,
    ( ! [X1] :
        ( r1_tarski(k9_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),X1),k9_relat_1(sK2,k2_relat_1(sK2)))
        | ~ v1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2))) )
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f98,f51])).

fof(f98,plain,
    ( ! [X1] :
        ( r1_tarski(k9_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),X1),k2_relat_1(k7_relat_1(sK2,k2_relat_1(sK2))))
        | ~ v1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2))) )
    | ~ spl3_4 ),
    inference(superposition,[],[f30,f92])).

fof(f104,plain,
    ( ~ spl3_4
    | spl3_7
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f97,f75,f47,f102,f75])).

fof(f97,plain,
    ( ! [X0] :
        ( r1_tarski(k9_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),X0),k9_relat_1(sK2,k2_relat_1(sK2)))
        | ~ v1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2))) )
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(superposition,[],[f54,f92])).

fof(f90,plain,
    ( ~ spl3_2
    | spl3_4 ),
    inference(avatar_split_clause,[],[f89,f75,f47])).

fof(f89,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_4 ),
    inference(resolution,[],[f77,f29])).

fof(f77,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f88,plain,
    ( ~ spl3_4
    | spl3_6
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f72,f56,f47,f86,f75])).

fof(f86,plain,
    ( spl3_6
  <=> ! [X2] : v1_relat_1(k7_relat_1(sK2,k9_relat_1(sK2,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f72,plain,
    ( ! [X2] :
        ( v1_relat_1(k7_relat_1(sK2,k9_relat_1(sK2,X2)))
        | ~ v1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2))) )
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f29,f69])).

fof(f84,plain,
    ( ~ spl3_4
    | spl3_5
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f83,f56,f47,f79,f75])).

fof(f79,plain,
    ( spl3_5
  <=> ! [X0] : r1_tarski(k9_relat_1(sK2,k9_relat_1(sK2,X0)),k9_relat_1(sK2,k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f83,plain,
    ( ! [X1] :
        ( r1_tarski(k9_relat_1(sK2,k9_relat_1(sK2,X1)),k9_relat_1(sK2,k2_relat_1(sK2)))
        | ~ v1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2))) )
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f82,f51])).

fof(f82,plain,
    ( ! [X1] :
        ( r1_tarski(k2_relat_1(k7_relat_1(sK2,k9_relat_1(sK2,X1))),k9_relat_1(sK2,k2_relat_1(sK2)))
        | ~ v1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2))) )
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f71,f51])).

fof(f71,plain,
    ( ! [X1] :
        ( r1_tarski(k2_relat_1(k7_relat_1(sK2,k9_relat_1(sK2,X1))),k2_relat_1(k7_relat_1(sK2,k2_relat_1(sK2))))
        | ~ v1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2))) )
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f30,f69])).

fof(f81,plain,
    ( ~ spl3_4
    | spl3_5
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f73,f56,f47,f79,f75])).

fof(f73,plain,
    ( ! [X0] :
        ( r1_tarski(k9_relat_1(sK2,k9_relat_1(sK2,X0)),k9_relat_1(sK2,k2_relat_1(sK2)))
        | ~ v1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2))) )
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f70,f51])).

fof(f70,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k7_relat_1(sK2,k9_relat_1(sK2,X0))),k9_relat_1(sK2,k2_relat_1(sK2)))
        | ~ v1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2))) )
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f54,f69])).

fof(f58,plain,
    ( ~ spl3_2
    | spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f53,f47,f56,f47])).

fof(f53,plain,
    ( ! [X0] :
        ( r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl3_2 ),
    inference(superposition,[],[f30,f51])).

fof(f50,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f23,f47])).

fof(f23,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

fof(f45,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f37,f42])).

fof(f37,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
    inference(definition_unfolding,[],[f24,f36,f36])).

fof(f24,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:45:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.41  % (29736)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (29743)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.47  % (29728)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (29731)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (29729)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (29736)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f307,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f45,f50,f58,f81,f84,f88,f90,f104,f106,f125,f160,f162,f228,f232,f263,f264,f302,f306])).
% 0.20/0.48  fof(f306,plain,(
% 0.20/0.48    ~spl3_2 | spl3_14),
% 0.20/0.48    inference(avatar_split_clause,[],[f305,f299,f47])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    spl3_2 <=> v1_relat_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.48  fof(f299,plain,(
% 0.20/0.48    spl3_14 <=> v1_relat_1(k7_relat_1(sK2,sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.48  fof(f305,plain,(
% 0.20/0.48    ~v1_relat_1(sK2) | spl3_14),
% 0.20/0.48    inference(resolution,[],[f301,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.48  fof(f301,plain,(
% 0.20/0.48    ~v1_relat_1(k7_relat_1(sK2,sK1)) | spl3_14),
% 0.20/0.48    inference(avatar_component_clause,[],[f299])).
% 0.20/0.48  fof(f302,plain,(
% 0.20/0.48    ~spl3_14 | ~spl3_2 | spl3_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f293,f122,f47,f299])).
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    spl3_9 <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.48  fof(f293,plain,(
% 0.20/0.48    ~v1_relat_1(k7_relat_1(sK2,sK1)) | (~spl3_2 | spl3_9)),
% 0.20/0.48    inference(resolution,[],[f222,f124])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK1)) | spl3_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f122])).
% 0.20/0.48  fof(f222,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X1,X1,X1,X0))),k9_relat_1(sK2,X0)) | ~v1_relat_1(k7_relat_1(sK2,X0))) ) | ~spl3_2),
% 0.20/0.48    inference(superposition,[],[f180,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f26,f36,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f27,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f28,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.48  fof(f180,plain,(
% 0.20/0.48    ( ! [X2,X1] : (r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),k9_relat_1(sK2,X1)) | ~v1_relat_1(k7_relat_1(sK2,X1))) ) | ~spl3_2),
% 0.20/0.48    inference(forward_demodulation,[],[f175,f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) ) | ~spl3_2),
% 0.20/0.48    inference(resolution,[],[f31,f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    v1_relat_1(sK2) | ~spl3_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f47])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.48  fof(f175,plain,(
% 0.20/0.48    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(sK2,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))),k9_relat_1(sK2,X1)) | ~v1_relat_1(k7_relat_1(sK2,X1))) ) | ~spl3_2),
% 0.20/0.48    inference(superposition,[],[f54,f65])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k7_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k7_relat_1(sK2,X0),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) ) | ~spl3_2),
% 0.20/0.48    inference(resolution,[],[f63,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f25,f36])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X1),X0)) ) | ~spl3_2),
% 0.20/0.48    inference(resolution,[],[f33,f49])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(flattening,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2)),k9_relat_1(sK2,X1)) | ~v1_relat_1(k7_relat_1(sK2,X1))) ) | ~spl3_2),
% 0.20/0.48    inference(superposition,[],[f30,f51])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).
% 0.20/0.48  fof(f264,plain,(
% 0.20/0.48    spl3_13 | ~spl3_2 | ~spl3_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f256,f118,f47,f260])).
% 0.20/0.48  fof(f260,plain,(
% 0.20/0.48    spl3_13 <=> k7_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) = k7_relat_1(k7_relat_1(sK2,k9_relat_1(sK2,sK0)),k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    spl3_8 <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.48  fof(f256,plain,(
% 0.20/0.48    k7_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) = k7_relat_1(k7_relat_1(sK2,k9_relat_1(sK2,sK0)),k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) | (~spl3_2 | ~spl3_8)),
% 0.20/0.48    inference(resolution,[],[f119,f63])).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) | ~spl3_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f118])).
% 0.20/0.48  fof(f263,plain,(
% 0.20/0.48    spl3_13 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f258,f118,f75,f56,f47,f260])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    spl3_3 <=> ! [X0] : r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    spl3_4 <=> v1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.48  fof(f258,plain,(
% 0.20/0.48    k7_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) = k7_relat_1(k7_relat_1(sK2,k9_relat_1(sK2,sK0)),k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_8)),
% 0.20/0.48    inference(forward_demodulation,[],[f257,f69])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    ( ! [X8] : (k7_relat_1(sK2,k9_relat_1(sK2,X8)) = k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k9_relat_1(sK2,X8))) ) | (~spl3_2 | ~spl3_3)),
% 0.20/0.48    inference(resolution,[],[f63,f57])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(sK2))) ) | ~spl3_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f56])).
% 0.20/0.48  fof(f257,plain,(
% 0.20/0.48    k7_relat_1(k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k9_relat_1(sK2,sK0)),k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) = k7_relat_1(sK2,k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_8)),
% 0.20/0.48    inference(forward_demodulation,[],[f255,f69])).
% 0.20/0.48  fof(f255,plain,(
% 0.20/0.48    k7_relat_1(k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k9_relat_1(sK2,sK0)),k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) = k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) | (~spl3_4 | ~spl3_8)),
% 0.20/0.48    inference(resolution,[],[f119,f91])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),X1),X0) = k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),X0)) ) | ~spl3_4),
% 0.20/0.48    inference(resolution,[],[f76,f33])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    v1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2))) | ~spl3_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f75])).
% 0.20/0.48  fof(f232,plain,(
% 0.20/0.48    ~spl3_2 | spl3_12),
% 0.20/0.48    inference(avatar_split_clause,[],[f231,f225,f47])).
% 0.20/0.48  % (29740)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  fof(f225,plain,(
% 0.20/0.48    spl3_12 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.48  fof(f231,plain,(
% 0.20/0.48    ~v1_relat_1(sK2) | spl3_12),
% 0.20/0.48    inference(resolution,[],[f227,f29])).
% 0.20/0.48  fof(f227,plain,(
% 0.20/0.48    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl3_12),
% 0.20/0.48    inference(avatar_component_clause,[],[f225])).
% 0.20/0.48  fof(f228,plain,(
% 0.20/0.48    ~spl3_12 | ~spl3_2 | spl3_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f219,f118,f47,f225])).
% 0.20/0.48  fof(f219,plain,(
% 0.20/0.48    ~v1_relat_1(k7_relat_1(sK2,sK0)) | (~spl3_2 | spl3_8)),
% 0.20/0.48    inference(resolution,[],[f180,f120])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) | spl3_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f118])).
% 0.20/0.48  fof(f162,plain,(
% 0.20/0.48    ~spl3_4 | spl3_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f161,f154,f75])).
% 0.20/0.48  fof(f154,plain,(
% 0.20/0.48    spl3_10 <=> v1_relat_1(k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k2_relat_1(sK2)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.48  fof(f161,plain,(
% 0.20/0.48    ~v1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2))) | spl3_10),
% 0.20/0.48    inference(resolution,[],[f156,f29])).
% 0.20/0.48  fof(f156,plain,(
% 0.20/0.48    ~v1_relat_1(k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k2_relat_1(sK2))) | spl3_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f154])).
% 0.20/0.48  fof(f160,plain,(
% 0.20/0.48    ~spl3_10 | spl3_11 | ~spl3_2 | ~spl3_3 | ~spl3_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f152,f75,f56,f47,f158,f154])).
% 0.20/0.48  fof(f158,plain,(
% 0.20/0.48    spl3_11 <=> ! [X0] : r1_tarski(k9_relat_1(sK2,k9_relat_1(sK2,X0)),k9_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k2_relat_1(sK2)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.48  fof(f152,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k9_relat_1(sK2,k9_relat_1(sK2,X0)),k9_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k2_relat_1(sK2))) | ~v1_relat_1(k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k2_relat_1(sK2)))) ) | (~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.20/0.48    inference(forward_demodulation,[],[f151,f51])).
% 0.20/0.48  fof(f151,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK2,k9_relat_1(sK2,X0))),k9_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k2_relat_1(sK2))) | ~v1_relat_1(k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k2_relat_1(sK2)))) ) | (~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.20/0.48    inference(forward_demodulation,[],[f149,f92])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    ( ! [X2] : (k2_relat_1(k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),X2)) = k9_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),X2)) ) | ~spl3_4),
% 0.20/0.48    inference(resolution,[],[f76,f31])).
% 0.20/0.48  fof(f149,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK2,k9_relat_1(sK2,X0))),k2_relat_1(k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k2_relat_1(sK2)))) | ~v1_relat_1(k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k2_relat_1(sK2)))) ) | (~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.20/0.48    inference(superposition,[],[f30,f144])).
% 0.20/0.48  fof(f144,plain,(
% 0.20/0.48    ( ! [X11] : (k7_relat_1(k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k2_relat_1(sK2)),k9_relat_1(sK2,X11)) = k7_relat_1(sK2,k9_relat_1(sK2,X11))) ) | (~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.20/0.48    inference(forward_demodulation,[],[f140,f69])).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    ( ! [X11] : (k7_relat_1(k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k2_relat_1(sK2)),k9_relat_1(sK2,X11)) = k7_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),k9_relat_1(sK2,X11))) ) | (~spl3_3 | ~spl3_4)),
% 0.20/0.48    inference(resolution,[],[f91,f57])).
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    ~spl3_8 | ~spl3_9 | spl3_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f113,f42,f122,f118])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    spl3_1 <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK1)) | ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) | spl3_1),
% 0.20/0.48    inference(resolution,[],[f40,f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) | spl3_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f42])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f34,f36])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(flattening,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    ~spl3_4 | spl3_7 | ~spl3_2 | ~spl3_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f105,f75,f47,f102,f75])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    spl3_7 <=> ! [X0] : r1_tarski(k9_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),X0),k9_relat_1(sK2,k2_relat_1(sK2)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    ( ! [X1] : (r1_tarski(k9_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),X1),k9_relat_1(sK2,k2_relat_1(sK2))) | ~v1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)))) ) | (~spl3_2 | ~spl3_4)),
% 0.20/0.48    inference(forward_demodulation,[],[f98,f51])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    ( ! [X1] : (r1_tarski(k9_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),X1),k2_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)))) | ~v1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)))) ) | ~spl3_4),
% 0.20/0.48    inference(superposition,[],[f30,f92])).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    ~spl3_4 | spl3_7 | ~spl3_2 | ~spl3_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f97,f75,f47,f102,f75])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k9_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)),X0),k9_relat_1(sK2,k2_relat_1(sK2))) | ~v1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)))) ) | (~spl3_2 | ~spl3_4)),
% 0.20/0.48    inference(superposition,[],[f54,f92])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    ~spl3_2 | spl3_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f89,f75,f47])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    ~v1_relat_1(sK2) | spl3_4),
% 0.20/0.48    inference(resolution,[],[f77,f29])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    ~v1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2))) | spl3_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f75])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    ~spl3_4 | spl3_6 | ~spl3_2 | ~spl3_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f72,f56,f47,f86,f75])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    spl3_6 <=> ! [X2] : v1_relat_1(k7_relat_1(sK2,k9_relat_1(sK2,X2)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    ( ! [X2] : (v1_relat_1(k7_relat_1(sK2,k9_relat_1(sK2,X2))) | ~v1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)))) ) | (~spl3_2 | ~spl3_3)),
% 0.20/0.48    inference(superposition,[],[f29,f69])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    ~spl3_4 | spl3_5 | ~spl3_2 | ~spl3_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f83,f56,f47,f79,f75])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    spl3_5 <=> ! [X0] : r1_tarski(k9_relat_1(sK2,k9_relat_1(sK2,X0)),k9_relat_1(sK2,k2_relat_1(sK2)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    ( ! [X1] : (r1_tarski(k9_relat_1(sK2,k9_relat_1(sK2,X1)),k9_relat_1(sK2,k2_relat_1(sK2))) | ~v1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)))) ) | (~spl3_2 | ~spl3_3)),
% 0.20/0.48    inference(forward_demodulation,[],[f82,f51])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    ( ! [X1] : (r1_tarski(k2_relat_1(k7_relat_1(sK2,k9_relat_1(sK2,X1))),k9_relat_1(sK2,k2_relat_1(sK2))) | ~v1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)))) ) | (~spl3_2 | ~spl3_3)),
% 0.20/0.48    inference(forward_demodulation,[],[f71,f51])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    ( ! [X1] : (r1_tarski(k2_relat_1(k7_relat_1(sK2,k9_relat_1(sK2,X1))),k2_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)))) | ~v1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)))) ) | (~spl3_2 | ~spl3_3)),
% 0.20/0.48    inference(superposition,[],[f30,f69])).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    ~spl3_4 | spl3_5 | ~spl3_2 | ~spl3_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f73,f56,f47,f79,f75])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k9_relat_1(sK2,k9_relat_1(sK2,X0)),k9_relat_1(sK2,k2_relat_1(sK2))) | ~v1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)))) ) | (~spl3_2 | ~spl3_3)),
% 0.20/0.48    inference(forward_demodulation,[],[f70,f51])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK2,k9_relat_1(sK2,X0))),k9_relat_1(sK2,k2_relat_1(sK2))) | ~v1_relat_1(k7_relat_1(sK2,k2_relat_1(sK2)))) ) | (~spl3_2 | ~spl3_3)),
% 0.20/0.48    inference(superposition,[],[f54,f69])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ~spl3_2 | spl3_3 | ~spl3_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f53,f47,f56,f47])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | ~spl3_2),
% 0.20/0.48    inference(superposition,[],[f30,f51])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    spl3_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f23,f47])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    v1_relat_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.20/0.48    inference(negated_conjecture,[],[f11])).
% 0.20/0.48  fof(f11,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ~spl3_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f37,f42])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))),
% 0.20/0.48    inference(definition_unfolding,[],[f24,f36,f36])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (29736)------------------------------
% 0.20/0.48  % (29736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (29736)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (29736)Memory used [KB]: 6524
% 0.20/0.48  % (29736)Time elapsed: 0.076 s
% 0.20/0.48  % (29736)------------------------------
% 0.20/0.48  % (29736)------------------------------
% 0.20/0.49  % (29725)Success in time 0.131 s
%------------------------------------------------------------------------------
