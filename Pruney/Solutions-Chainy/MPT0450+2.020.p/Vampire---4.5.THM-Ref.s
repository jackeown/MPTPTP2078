%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 318 expanded)
%              Number of leaves         :   37 ( 130 expanded)
%              Depth                    :    9
%              Number of atoms          :  345 ( 656 expanded)
%              Number of equality atoms :   31 ( 160 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f279,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f66,f74,f78,f82,f86,f103,f115,f125,f139,f146,f154,f161,f168,f179,f185,f233,f238,f247,f256,f277])).

fof(f277,plain,
    ( ~ spl2_14
    | spl2_32
    | ~ spl2_34 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | ~ spl2_14
    | spl2_32
    | ~ spl2_34 ),
    inference(subsumption_resolution,[],[f246,f275])).

fof(f275,plain,
    ( ! [X0,X1] : r1_tarski(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1)
    | ~ spl2_14
    | ~ spl2_34 ),
    inference(forward_demodulation,[],[f271,f124])).

fof(f124,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl2_14
  <=> ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f271,plain,
    ( ! [X0,X1] : r1_tarski(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k2_xboole_0(X1,X1))
    | ~ spl2_14
    | ~ spl2_34 ),
    inference(superposition,[],[f255,f124])).

fof(f255,plain,
    ( ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X2))),k2_xboole_0(X1,X2))
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl2_34
  <=> ! [X1,X0,X2] : r1_tarski(k2_xboole_0(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X2))),k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f246,plain,
    ( ~ r1_tarski(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1)
    | spl2_32 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl2_32
  <=> r1_tarski(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f256,plain,(
    spl2_34 ),
    inference(avatar_split_clause,[],[f55,f254])).

fof(f55,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X2))),k2_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f41,f50,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f43,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f41,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f247,plain,
    ( ~ spl2_32
    | ~ spl2_2
    | ~ spl2_10
    | ~ spl2_24
    | spl2_31 ),
    inference(avatar_split_clause,[],[f242,f230,f183,f101,f63,f244])).

fof(f63,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f101,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f183,plain,
    ( spl2_24
  <=> ! [X0] : v1_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f230,plain,
    ( spl2_31
  <=> r1_tarski(k3_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f242,plain,
    ( ~ r1_tarski(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1)
    | ~ spl2_2
    | ~ spl2_10
    | ~ spl2_24
    | spl2_31 ),
    inference(subsumption_resolution,[],[f241,f184])).

fof(f184,plain,
    ( ! [X0] : v1_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0)))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f183])).

fof(f241,plain,
    ( ~ r1_tarski(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1)
    | ~ v1_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ spl2_2
    | ~ spl2_10
    | spl2_31 ),
    inference(subsumption_resolution,[],[f240,f65])).

fof(f65,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f240,plain,
    ( ~ r1_tarski(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ spl2_10
    | spl2_31 ),
    inference(resolution,[],[f232,f102])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f101])).

fof(f232,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_relat_1(sK1))
    | spl2_31 ),
    inference(avatar_component_clause,[],[f230])).

fof(f238,plain,
    ( ~ spl2_1
    | ~ spl2_7
    | ~ spl2_10
    | ~ spl2_24
    | spl2_30 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_10
    | ~ spl2_24
    | spl2_30 ),
    inference(subsumption_resolution,[],[f236,f184])).

fof(f236,plain,
    ( ~ v1_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_10
    | spl2_30 ),
    inference(subsumption_resolution,[],[f235,f60])).

fof(f60,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl2_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f235,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ spl2_7
    | ~ spl2_10
    | spl2_30 ),
    inference(subsumption_resolution,[],[f234,f85])).

fof(f85,plain,
    ( ! [X0,X1] : r1_tarski(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl2_7
  <=> ! [X1,X0] : r1_tarski(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f234,plain,
    ( ~ r1_tarski(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ spl2_10
    | spl2_30 ),
    inference(resolution,[],[f228,f102])).

fof(f228,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_relat_1(sK0))
    | spl2_30 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl2_30
  <=> r1_tarski(k3_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f233,plain,
    ( ~ spl2_30
    | ~ spl2_31
    | ~ spl2_17
    | spl2_23 ),
    inference(avatar_split_clause,[],[f224,f176,f137,f230,f226])).

fof(f137,plain,
    ( spl2_17
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f176,plain,
    ( spl2_23
  <=> r1_tarski(k3_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k5_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f224,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_relat_1(sK1))
    | ~ r1_tarski(k3_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_relat_1(sK0))
    | ~ spl2_17
    | spl2_23 ),
    inference(resolution,[],[f178,f138])).

fof(f138,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f137])).

fof(f178,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k5_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1))))
    | spl2_23 ),
    inference(avatar_component_clause,[],[f176])).

fof(f185,plain,
    ( spl2_24
    | ~ spl2_7
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f173,f166,f84,f183])).

fof(f166,plain,
    ( spl2_21
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f173,plain,
    ( ! [X0] : v1_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0)))
    | ~ spl2_7
    | ~ spl2_21 ),
    inference(resolution,[],[f167,f85])).

fof(f167,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | v1_relat_1(X0) )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f166])).

fof(f179,plain,(
    ~ spl2_23 ),
    inference(avatar_split_clause,[],[f51,f176])).

fof(f51,plain,(
    ~ r1_tarski(k3_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k5_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f30,f50,f50])).

fof(f30,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

fof(f168,plain,
    ( spl2_21
    | ~ spl2_1
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f162,f159,f58,f166])).

fof(f159,plain,
    ( spl2_20
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(X1,X0)
        | v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f162,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | v1_relat_1(X0) )
    | ~ spl2_1
    | ~ spl2_20 ),
    inference(resolution,[],[f160,f60])).

fof(f160,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(X1,X0)
        | v1_relat_1(X1) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f159])).

fof(f161,plain,
    ( spl2_20
    | ~ spl2_6
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f157,f152,f80,f159])).

fof(f80,plain,
    ( spl2_6
  <=> ! [X0] : k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f152,plain,
    ( spl2_19
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X0,X2)
        | v1_relat_1(X0)
        | ~ v1_relat_1(k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(X1,X0)
        | v1_relat_1(X1) )
    | ~ spl2_6
    | ~ spl2_19 ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(X1,X0)
        | v1_relat_1(X1)
        | ~ r1_tarski(X1,X0) )
    | ~ spl2_6
    | ~ spl2_19 ),
    inference(superposition,[],[f153,f81])).

fof(f81,plain,
    ( ! [X0] : k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f153,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))
        | ~ r1_tarski(X0,X2)
        | v1_relat_1(X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f152])).

fof(f154,plain,
    ( spl2_19
    | ~ spl2_5
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f147,f144,f76,f152])).

fof(f76,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f144,plain,
    ( spl2_18
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X0,X2)
        | m1_subset_1(X0,k1_zfmisc_1(k1_setfam_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f147,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X0,X2)
        | v1_relat_1(X0)
        | ~ v1_relat_1(k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) )
    | ~ spl2_5
    | ~ spl2_18 ),
    inference(resolution,[],[f145,f77])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f145,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(k1_setfam_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f144])).

fof(f146,plain,
    ( spl2_18
    | ~ spl2_4
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f140,f137,f72,f144])).

fof(f72,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f140,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X0,X2)
        | m1_subset_1(X0,k1_zfmisc_1(k1_setfam_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))) )
    | ~ spl2_4
    | ~ spl2_17 ),
    inference(resolution,[],[f138,f73])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f139,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f56,f137])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f50])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f125,plain,
    ( spl2_14
    | ~ spl2_6
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f121,f113,f80,f123])).

fof(f113,plain,
    ( spl2_12
  <=> ! [X1,X0] : k2_xboole_0(X0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f121,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl2_6
    | ~ spl2_12 ),
    inference(superposition,[],[f114,f81])).

fof(f114,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = X0
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f113])).

fof(f115,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f54,f113])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f35,f50])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f103,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f31,f101])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
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
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f86,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f53,f84])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f34,f50])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f82,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f52,f80])).

fof(f52,plain,(
    ! [X0] : k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f33,f50])).

fof(f33,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f78,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f32,f76])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f74,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f39,f72])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f66,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f29,f63])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f28,f58])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:49:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (15148)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (15148)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (15155)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f279,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f61,f66,f74,f78,f82,f86,f103,f115,f125,f139,f146,f154,f161,f168,f179,f185,f233,f238,f247,f256,f277])).
% 0.21/0.49  fof(f277,plain,(
% 0.21/0.49    ~spl2_14 | spl2_32 | ~spl2_34),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f276])).
% 0.21/0.49  fof(f276,plain,(
% 0.21/0.49    $false | (~spl2_14 | spl2_32 | ~spl2_34)),
% 0.21/0.49    inference(subsumption_resolution,[],[f246,f275])).
% 0.21/0.49  fof(f275,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1)) ) | (~spl2_14 | ~spl2_34)),
% 0.21/0.49    inference(forward_demodulation,[],[f271,f124])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) ) | ~spl2_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f123])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    spl2_14 <=> ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.49  fof(f271,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k2_xboole_0(X1,X1))) ) | (~spl2_14 | ~spl2_34)),
% 0.21/0.49    inference(superposition,[],[f255,f124])).
% 0.21/0.49  fof(f255,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X2))),k2_xboole_0(X1,X2))) ) | ~spl2_34),
% 0.21/0.49    inference(avatar_component_clause,[],[f254])).
% 0.21/0.49  fof(f254,plain,(
% 0.21/0.49    spl2_34 <=> ! [X1,X0,X2] : r1_tarski(k2_xboole_0(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X2))),k2_xboole_0(X1,X2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.21/0.49  fof(f246,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1) | spl2_32),
% 0.21/0.49    inference(avatar_component_clause,[],[f244])).
% 0.21/0.49  fof(f244,plain,(
% 0.21/0.49    spl2_32 <=> r1_tarski(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.21/0.49  fof(f256,plain,(
% 0.21/0.49    spl2_34),
% 0.21/0.49    inference(avatar_split_clause,[],[f55,f254])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X2))),k2_xboole_0(X1,X2))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f41,f50,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f36,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f37,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f40,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f43,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f44,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.21/0.49  fof(f247,plain,(
% 0.21/0.49    ~spl2_32 | ~spl2_2 | ~spl2_10 | ~spl2_24 | spl2_31),
% 0.21/0.49    inference(avatar_split_clause,[],[f242,f230,f183,f101,f63,f244])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    spl2_2 <=> v1_relat_1(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    spl2_10 <=> ! [X1,X0] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    spl2_24 <=> ! [X0] : v1_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    spl2_31 <=> r1_tarski(k3_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_relat_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.21/0.49  fof(f242,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1) | (~spl2_2 | ~spl2_10 | ~spl2_24 | spl2_31)),
% 0.21/0.49    inference(subsumption_resolution,[],[f241,f184])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0)))) ) | ~spl2_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f183])).
% 0.21/0.49  fof(f241,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1) | ~v1_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | (~spl2_2 | ~spl2_10 | spl2_31)),
% 0.21/0.49    inference(subsumption_resolution,[],[f240,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    v1_relat_1(sK1) | ~spl2_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f63])).
% 0.21/0.49  fof(f240,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | (~spl2_10 | spl2_31)),
% 0.21/0.49    inference(resolution,[],[f232,f102])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f101])).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    ~r1_tarski(k3_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_relat_1(sK1)) | spl2_31),
% 0.21/0.49    inference(avatar_component_clause,[],[f230])).
% 0.21/0.49  fof(f238,plain,(
% 0.21/0.49    ~spl2_1 | ~spl2_7 | ~spl2_10 | ~spl2_24 | spl2_30),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f237])).
% 0.21/0.49  fof(f237,plain,(
% 0.21/0.49    $false | (~spl2_1 | ~spl2_7 | ~spl2_10 | ~spl2_24 | spl2_30)),
% 0.21/0.49    inference(subsumption_resolution,[],[f236,f184])).
% 0.21/0.49  fof(f236,plain,(
% 0.21/0.49    ~v1_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | (~spl2_1 | ~spl2_7 | ~spl2_10 | spl2_30)),
% 0.21/0.49    inference(subsumption_resolution,[],[f235,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    v1_relat_1(sK0) | ~spl2_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    spl2_1 <=> v1_relat_1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.49  fof(f235,plain,(
% 0.21/0.49    ~v1_relat_1(sK0) | ~v1_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | (~spl2_7 | ~spl2_10 | spl2_30)),
% 0.21/0.49    inference(subsumption_resolution,[],[f234,f85])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X0)) ) | ~spl2_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f84])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    spl2_7 <=> ! [X1,X0] : r1_tarski(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.49  fof(f234,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | (~spl2_10 | spl2_30)),
% 0.21/0.49    inference(resolution,[],[f228,f102])).
% 0.21/0.49  fof(f228,plain,(
% 0.21/0.49    ~r1_tarski(k3_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_relat_1(sK0)) | spl2_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f226])).
% 0.21/0.49  fof(f226,plain,(
% 0.21/0.49    spl2_30 <=> r1_tarski(k3_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_relat_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    ~spl2_30 | ~spl2_31 | ~spl2_17 | spl2_23),
% 0.21/0.49    inference(avatar_split_clause,[],[f224,f176,f137,f230,f226])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    spl2_17 <=> ! [X1,X0,X2] : (r1_tarski(X0,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    spl2_23 <=> r1_tarski(k3_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k5_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    ~r1_tarski(k3_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_relat_1(sK1)) | ~r1_tarski(k3_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_relat_1(sK0)) | (~spl2_17 | spl2_23)),
% 0.21/0.49    inference(resolution,[],[f178,f138])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl2_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f137])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    ~r1_tarski(k3_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k5_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1)))) | spl2_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f176])).
% 0.21/0.49  fof(f185,plain,(
% 0.21/0.49    spl2_24 | ~spl2_7 | ~spl2_21),
% 0.21/0.49    inference(avatar_split_clause,[],[f173,f166,f84,f183])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    spl2_21 <=> ! [X0] : (~r1_tarski(X0,sK0) | v1_relat_1(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0)))) ) | (~spl2_7 | ~spl2_21)),
% 0.21/0.49    inference(resolution,[],[f167,f85])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,sK0) | v1_relat_1(X0)) ) | ~spl2_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f166])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    ~spl2_23),
% 0.21/0.49    inference(avatar_split_clause,[],[f51,f176])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ~r1_tarski(k3_relat_1(k1_setfam_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k5_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1))))),
% 0.21/0.49    inference(definition_unfolding,[],[f30,f50,f50])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f25,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f15])).
% 0.21/0.49  fof(f15,conjecture,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    spl2_21 | ~spl2_1 | ~spl2_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f162,f159,f58,f166])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    spl2_20 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~r1_tarski(X1,X0) | v1_relat_1(X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,sK0) | v1_relat_1(X0)) ) | (~spl2_1 | ~spl2_20)),
% 0.21/0.49    inference(resolution,[],[f160,f60])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X1,X0) | v1_relat_1(X1)) ) | ~spl2_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f159])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    spl2_20 | ~spl2_6 | ~spl2_19),
% 0.21/0.49    inference(avatar_split_clause,[],[f157,f152,f80,f159])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    spl2_6 <=> ! [X0] : k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    spl2_19 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | v1_relat_1(X0) | ~v1_relat_1(k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X1,X0) | v1_relat_1(X1)) ) | (~spl2_6 | ~spl2_19)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f156])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X1,X0) | v1_relat_1(X1) | ~r1_tarski(X1,X0)) ) | (~spl2_6 | ~spl2_19)),
% 0.21/0.49    inference(superposition,[],[f153,f81])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ( ! [X0] : (k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0) ) | ~spl2_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f80])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | v1_relat_1(X0) | ~r1_tarski(X0,X1)) ) | ~spl2_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f152])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    spl2_19 | ~spl2_5 | ~spl2_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f147,f144,f76,f152])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl2_5 <=> ! [X1,X0] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    spl2_18 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | m1_subset_1(X0,k1_zfmisc_1(k1_setfam_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | v1_relat_1(X0) | ~v1_relat_1(k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))) ) | (~spl2_5 | ~spl2_18)),
% 0.21/0.49    inference(resolution,[],[f145,f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f76])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(k1_setfam_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl2_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f144])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    spl2_18 | ~spl2_4 | ~spl2_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f140,f137,f72,f144])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl2_4 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | m1_subset_1(X0,k1_zfmisc_1(k1_setfam_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))))) ) | (~spl2_4 | ~spl2_17)),
% 0.21/0.49    inference(resolution,[],[f138,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl2_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f72])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    spl2_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f56,f137])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f42,f50])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    spl2_14 | ~spl2_6 | ~spl2_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f121,f113,f80,f123])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    spl2_12 <=> ! [X1,X0] : k2_xboole_0(X0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = X0),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) ) | (~spl2_6 | ~spl2_12)),
% 0.21/0.49    inference(superposition,[],[f114,f81])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = X0) ) | ~spl2_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f113])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    spl2_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f54,f113])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = X0) )),
% 0.21/0.49    inference(definition_unfolding,[],[f35,f50])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    spl2_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f31,f101])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    spl2_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f53,f84])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f34,f50])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl2_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f52,f80])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0] : (k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 0.21/0.49    inference(definition_unfolding,[],[f33,f50])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.49    inference(rectify,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl2_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f32,f76])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    spl2_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f39,f72])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl2_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f29,f63])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    v1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    spl2_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f28,f58])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    v1_relat_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (15148)------------------------------
% 0.21/0.49  % (15148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (15148)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (15148)Memory used [KB]: 6268
% 0.21/0.49  % (15148)Time elapsed: 0.068 s
% 0.21/0.49  % (15148)------------------------------
% 0.21/0.49  % (15148)------------------------------
% 0.21/0.49  % (15134)Success in time 0.131 s
%------------------------------------------------------------------------------
