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
% DateTime   : Thu Dec  3 12:52:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  189 ( 387 expanded)
%              Number of leaves         :   48 ( 182 expanded)
%              Depth                    :   10
%              Number of atoms          :  512 ( 953 expanded)
%              Number of equality atoms :  133 ( 277 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f761,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f65,f69,f73,f77,f81,f85,f92,f98,f106,f110,f119,f123,f129,f141,f149,f162,f187,f195,f199,f213,f220,f226,f234,f249,f274,f278,f285,f296,f451,f683,f730])).

fof(f730,plain,
    ( ~ spl2_14
    | ~ spl2_25
    | spl2_31
    | ~ spl2_35
    | ~ spl2_51 ),
    inference(avatar_contradiction_clause,[],[f727])).

fof(f727,plain,
    ( $false
    | ~ spl2_14
    | ~ spl2_25
    | spl2_31
    | ~ spl2_35
    | ~ spl2_51 ),
    inference(subsumption_resolution,[],[f273,f726])).

fof(f726,plain,
    ( ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)))
    | ~ spl2_14
    | ~ spl2_25
    | ~ spl2_35
    | ~ spl2_51 ),
    inference(forward_demodulation,[],[f725,f219])).

fof(f219,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl2_25
  <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f725,plain,
    ( ! [X4,X3] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4))) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X4)
    | ~ spl2_14
    | ~ spl2_35
    | ~ spl2_51 ),
    inference(forward_demodulation,[],[f724,f128])).

fof(f128,plain,
    ( ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl2_14
  <=> ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f724,plain,
    ( ! [X4,X3] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X3),X4),X4)
    | ~ spl2_14
    | ~ spl2_35
    | ~ spl2_51 ),
    inference(forward_demodulation,[],[f723,f682])).

fof(f682,plain,
    ( ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))
    | ~ spl2_51 ),
    inference(avatar_component_clause,[],[f681])).

fof(f681,plain,
    ( spl2_51
  <=> ! [X1,X0,X2] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).

fof(f723,plain,
    ( ! [X4,X3] : k7_relat_1(k7_relat_1(k6_relat_1(X3),k1_relat_1(k7_relat_1(k6_relat_1(X3),X4))),X4) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)))
    | ~ spl2_14
    | ~ spl2_35
    | ~ spl2_51 ),
    inference(forward_demodulation,[],[f688,f295])).

fof(f295,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X3),X2) = k7_relat_1(k6_relat_1(X2),X3)
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl2_35
  <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X3),X2) = k7_relat_1(k6_relat_1(X2),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f688,plain,
    ( ! [X4,X3] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4))) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4))),X3),X4)
    | ~ spl2_14
    | ~ spl2_51 ),
    inference(superposition,[],[f682,f128])).

fof(f273,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))
    | spl2_31 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl2_31
  <=> k7_relat_1(k6_relat_1(sK0),sK1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f683,plain,
    ( spl2_51
    | ~ spl2_1
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f676,f449,f59,f681])).

fof(f59,plain,
    ( spl2_1
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f449,plain,
    ( spl2_45
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f676,plain,
    ( ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))
    | ~ spl2_1
    | ~ spl2_45 ),
    inference(resolution,[],[f450,f60])).

fof(f60,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f450,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f449])).

fof(f451,plain,
    ( spl2_45
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_23
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f241,f232,f197,f63,f59,f449])).

fof(f63,plain,
    ( spl2_2
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

% (12245)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
fof(f197,plain,
    ( spl2_23
  <=> ! [X1,X0] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f232,plain,
    ( spl2_27
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f241,plain,
    ( ! [X2,X0,X1] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))
        | ~ v1_relat_1(X2) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_23
    | ~ spl2_27 ),
    inference(backward_demodulation,[],[f233,f239])).

fof(f239,plain,
    ( ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f235,f64])).

fof(f64,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f235,plain,
    ( ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k2_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1))
    | ~ spl2_1
    | ~ spl2_23 ),
    inference(resolution,[],[f198,f60])).

fof(f198,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f197])).

fof(f233,plain,
    ( ! [X2,X0,X1] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
        | ~ v1_relat_1(X2) )
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f232])).

fof(f296,plain,
    ( spl2_35
    | ~ spl2_18
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f291,f283,f160,f294])).

fof(f160,plain,
    ( spl2_18
  <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f283,plain,
    ( spl2_33
  <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f291,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X3),X2) = k7_relat_1(k6_relat_1(X2),X3)
    | ~ spl2_18
    | ~ spl2_33 ),
    inference(superposition,[],[f284,f161])).

fof(f161,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f160])).

fof(f284,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f283])).

fof(f285,plain,
    ( spl2_33
    | ~ spl2_26
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f280,f276,f224,f283])).

fof(f224,plain,
    ( spl2_26
  <=> ! [X5,X7,X6] : k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) = k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f276,plain,
    ( spl2_32
  <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f280,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_26
    | ~ spl2_32 ),
    inference(superposition,[],[f225,f277])).

fof(f277,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f276])).

fof(f225,plain,
    ( ! [X6,X7,X5] : k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) = k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6)
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f224])).

fof(f278,plain,
    ( spl2_32
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f253,f247,f121,f117,f276])).

fof(f117,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = X1
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f121,plain,
    ( spl2_13
  <=> ! [X1,X2] : v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f247,plain,
    ( spl2_28
  <=> ! [X1,X0] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f253,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f250,f122])).

fof(f122,plain,
    ( ! [X2,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f121])).

fof(f250,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)
        | ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) )
    | ~ spl2_12
    | ~ spl2_28 ),
    inference(resolution,[],[f248,f118])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f117])).

fof(f248,plain,
    ( ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f247])).

fof(f274,plain,
    ( ~ spl2_31
    | ~ spl2_1
    | ~ spl2_2
    | spl2_10
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f240,f197,f103,f63,f59,f271])).

fof(f103,plain,
    ( spl2_10
  <=> k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f240,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl2_1
    | ~ spl2_2
    | spl2_10
    | ~ spl2_23 ),
    inference(backward_demodulation,[],[f105,f239])).

fof(f105,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)
    | spl2_10 ),
    inference(avatar_component_clause,[],[f103])).

fof(f249,plain,
    ( spl2_28
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f243,f197,f79,f63,f59,f247])).

fof(f79,plain,
    ( spl2_6
  <=> ! [X1,X0] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f243,plain,
    ( ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_23 ),
    inference(backward_demodulation,[],[f80,f239])).

fof(f80,plain,
    ( ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f234,plain,(
    spl2_27 ),
    inference(avatar_split_clause,[],[f57,f232])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f51,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f226,plain,
    ( spl2_26
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_17
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f207,f193,f147,f121,f108,f96,f71,f59,f224])).

fof(f71,plain,
    ( spl2_4
  <=> ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f96,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f108,plain,
    ( spl2_11
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f147,plain,
    ( spl2_17
  <=> ! [X1,X0] :
        ( k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f193,plain,
    ( spl2_22
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X0)
        | k7_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f207,plain,
    ( ! [X6,X7,X5] : k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) = k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_17
    | ~ spl2_22 ),
    inference(backward_demodulation,[],[f158,f204])).

fof(f204,plain,
    ( ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1))
    | ~ spl2_1
    | ~ spl2_11
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f200,f109])).

fof(f109,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f108])).

fof(f200,plain,
    ( ! [X2,X0,X1] : k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1))
    | ~ spl2_1
    | ~ spl2_22 ),
    inference(resolution,[],[f194,f60])).

fof(f194,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | k7_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f193])).

fof(f158,plain,
    ( ! [X6,X7,X5] : k5_relat_1(k7_relat_1(k6_relat_1(X7),X6),k6_relat_1(X5)) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f157,f124])).

fof(f124,plain,
    ( ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_9
    | ~ spl2_13 ),
    inference(resolution,[],[f122,f97])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f157,plain,
    ( ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k7_relat_1(k6_relat_1(X7),X6),k6_relat_1(X5))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f152,f155])).

fof(f155,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_11
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f154,f109])).

fof(f154,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_11
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f153,f109])).

fof(f153,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f150,f72])).

fof(f72,plain,
    ( ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f150,plain,
    ( ! [X0,X1] : k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X0))
    | ~ spl2_1
    | ~ spl2_17 ),
    inference(resolution,[],[f148,f60])).

fof(f148,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1)) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f147])).

fof(f152,plain,
    ( ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X6),X7)),k6_relat_1(X5))
    | ~ spl2_13
    | ~ spl2_17 ),
    inference(resolution,[],[f148,f122])).

fof(f220,plain,
    ( spl2_25
    | ~ spl2_11
    | ~ spl2_14
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f216,f211,f127,f108,f218])).

fof(f211,plain,
    ( spl2_24
  <=> ! [X1,X0,X2] : k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f216,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)
    | ~ spl2_11
    | ~ spl2_14
    | ~ spl2_24 ),
    inference(forward_demodulation,[],[f214,f109])).

fof(f214,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)
    | ~ spl2_14
    | ~ spl2_24 ),
    inference(superposition,[],[f212,f128])).

fof(f212,plain,
    ( ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f211])).

fof(f213,plain,
    ( spl2_24
    | ~ spl2_1
    | ~ spl2_11
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f204,f193,f108,f59,f211])).

fof(f199,plain,(
    spl2_23 ),
    inference(avatar_split_clause,[],[f56,f197])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f46,f53])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f195,plain,
    ( spl2_22
    | ~ spl2_1
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f188,f185,f59,f193])).

fof(f185,plain,
    ( spl2_21
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f188,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | k7_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) )
    | ~ spl2_1
    | ~ spl2_21 ),
    inference(resolution,[],[f186,f60])).

fof(f186,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f185])).

fof(f187,plain,(
    spl2_21 ),
    inference(avatar_split_clause,[],[f48,f185])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

fof(f162,plain,
    ( spl2_18
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_11
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f155,f147,f108,f71,f59,f160])).

fof(f149,plain,
    ( spl2_17
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f145,f139,f71,f59,f147])).

fof(f139,plain,
    ( spl2_16
  <=> ! [X1,X0] :
        ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f142,f72])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k6_relat_1(X1))) )
    | ~ spl2_1
    | ~ spl2_16 ),
    inference(resolution,[],[f140,f60])).

fof(f140,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f139])).

fof(f141,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f40,f139])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f129,plain,
    ( spl2_14
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f111,f108,f90,f127])).

fof(f90,plain,
    ( spl2_8
  <=> ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f111,plain,
    ( ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(superposition,[],[f109,f91])).

fof(f91,plain,
    ( ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f123,plain,
    ( spl2_13
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f115,f108,f75,f59,f121])).

fof(f75,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f115,plain,
    ( ! [X2,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f114,f60])).

fof(f114,plain,
    ( ! [X2,X1] :
        ( v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
        | ~ v1_relat_1(k6_relat_1(X1)) )
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f113,f60])).

fof(f113,plain,
    ( ! [X2,X1] :
        ( v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
        | ~ v1_relat_1(k6_relat_1(X2))
        | ~ v1_relat_1(k6_relat_1(X1)) )
    | ~ spl2_5
    | ~ spl2_11 ),
    inference(superposition,[],[f76,f109])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f119,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f47,f117])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f110,plain,
    ( spl2_11
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f99,f96,f59,f108])).

fof(f99,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(resolution,[],[f97,f60])).

fof(f106,plain,
    ( ~ spl2_10
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f101,f96,f59,f103])).

fof(f101,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(backward_demodulation,[],[f54,f99])).

fof(f54,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f34,f53])).

fof(f34,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f32])).

fof(f32,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f98,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f45,f96])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f92,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f88,f83,f67,f59,f90])).

fof(f67,plain,
    ( spl2_3
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f83,plain,
    ( spl2_7
  <=> ! [X0] :
        ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

% (12245)Refutation not found, incomplete strategy% (12245)------------------------------
% (12245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12245)Termination reason: Refutation not found, incomplete strategy

fof(f88,plain,
    ( ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f86,f68])).

fof(f68,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f67])).

% (12245)Memory used [KB]: 10618
% (12245)Time elapsed: 0.092 s
% (12245)------------------------------
% (12245)------------------------------
fof(f86,plain,
    ( ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0))))
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(resolution,[],[f84,f60])).

fof(f84,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f83])).

fof(f85,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f39,f83])).

fof(f39,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f81,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f55,f79])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f42,f53])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f77,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f49,f75])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f73,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f35,f71])).

fof(f35,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(f69,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f38,f67])).

fof(f38,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f65,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f37,f63])).

fof(f37,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f61,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f36,f59])).

fof(f36,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n014.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:40:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (12242)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.46  % (12238)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (12239)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (12249)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (12234)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (12235)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (12241)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (12237)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (12246)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (12247)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (12243)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (12240)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (12236)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.50  % (12241)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f761,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f61,f65,f69,f73,f77,f81,f85,f92,f98,f106,f110,f119,f123,f129,f141,f149,f162,f187,f195,f199,f213,f220,f226,f234,f249,f274,f278,f285,f296,f451,f683,f730])).
% 0.22/0.50  fof(f730,plain,(
% 0.22/0.50    ~spl2_14 | ~spl2_25 | spl2_31 | ~spl2_35 | ~spl2_51),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f727])).
% 0.22/0.50  fof(f727,plain,(
% 0.22/0.50    $false | (~spl2_14 | ~spl2_25 | spl2_31 | ~spl2_35 | ~spl2_51)),
% 0.22/0.50    inference(subsumption_resolution,[],[f273,f726])).
% 0.22/0.50  fof(f726,plain,(
% 0.22/0.50    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)))) ) | (~spl2_14 | ~spl2_25 | ~spl2_35 | ~spl2_51)),
% 0.22/0.50    inference(forward_demodulation,[],[f725,f219])).
% 0.22/0.50  fof(f219,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)) ) | ~spl2_25),
% 0.22/0.50    inference(avatar_component_clause,[],[f218])).
% 0.22/0.50  fof(f218,plain,(
% 0.22/0.50    spl2_25 <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.22/0.50  fof(f725,plain,(
% 0.22/0.50    ( ! [X4,X3] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4))) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X4)) ) | (~spl2_14 | ~spl2_35 | ~spl2_51)),
% 0.22/0.50    inference(forward_demodulation,[],[f724,f128])).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) ) | ~spl2_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f127])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    spl2_14 <=> ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.50  fof(f724,plain,(
% 0.22/0.50    ( ! [X4,X3] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X3),X4),X4)) ) | (~spl2_14 | ~spl2_35 | ~spl2_51)),
% 0.22/0.50    inference(forward_demodulation,[],[f723,f682])).
% 0.22/0.50  fof(f682,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))) ) | ~spl2_51),
% 0.22/0.50    inference(avatar_component_clause,[],[f681])).
% 0.22/0.50  fof(f681,plain,(
% 0.22/0.50    spl2_51 <=> ! [X1,X0,X2] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).
% 0.22/0.50  fof(f723,plain,(
% 0.22/0.50    ( ! [X4,X3] : (k7_relat_1(k7_relat_1(k6_relat_1(X3),k1_relat_1(k7_relat_1(k6_relat_1(X3),X4))),X4) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)))) ) | (~spl2_14 | ~spl2_35 | ~spl2_51)),
% 0.22/0.50    inference(forward_demodulation,[],[f688,f295])).
% 0.22/0.50  fof(f295,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X3),X2) = k7_relat_1(k6_relat_1(X2),X3)) ) | ~spl2_35),
% 0.22/0.50    inference(avatar_component_clause,[],[f294])).
% 0.22/0.50  fof(f294,plain,(
% 0.22/0.50    spl2_35 <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X3),X2) = k7_relat_1(k6_relat_1(X2),X3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 0.22/0.50  fof(f688,plain,(
% 0.22/0.50    ( ! [X4,X3] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4))) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4))),X3),X4)) ) | (~spl2_14 | ~spl2_51)),
% 0.22/0.50    inference(superposition,[],[f682,f128])).
% 0.22/0.50  fof(f273,plain,(
% 0.22/0.50    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) | spl2_31),
% 0.22/0.50    inference(avatar_component_clause,[],[f271])).
% 0.22/0.50  fof(f271,plain,(
% 0.22/0.50    spl2_31 <=> k7_relat_1(k6_relat_1(sK0),sK1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.22/0.50  fof(f683,plain,(
% 0.22/0.50    spl2_51 | ~spl2_1 | ~spl2_45),
% 0.22/0.50    inference(avatar_split_clause,[],[f676,f449,f59,f681])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    spl2_1 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.50  fof(f449,plain,(
% 0.22/0.50    spl2_45 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) | ~v1_relat_1(X2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 0.22/0.50  fof(f676,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))) ) | (~spl2_1 | ~spl2_45)),
% 0.22/0.50    inference(resolution,[],[f450,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f59])).
% 0.22/0.50  fof(f450,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) ) | ~spl2_45),
% 0.22/0.50    inference(avatar_component_clause,[],[f449])).
% 0.22/0.50  fof(f451,plain,(
% 0.22/0.50    spl2_45 | ~spl2_1 | ~spl2_2 | ~spl2_23 | ~spl2_27),
% 0.22/0.50    inference(avatar_split_clause,[],[f241,f232,f197,f63,f59,f449])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    spl2_2 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.51  % (12245)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.51  fof(f197,plain,(
% 0.22/0.51    spl2_23 <=> ! [X1,X0] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.22/0.51  fof(f232,plain,(
% 0.22/0.51    spl2_27 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.22/0.51  fof(f241,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) | ~v1_relat_1(X2)) ) | (~spl2_1 | ~spl2_2 | ~spl2_23 | ~spl2_27)),
% 0.22/0.51    inference(backward_demodulation,[],[f233,f239])).
% 0.22/0.51  fof(f239,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_1 | ~spl2_2 | ~spl2_23)),
% 0.22/0.51    inference(forward_demodulation,[],[f235,f64])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f63])).
% 0.22/0.51  fof(f235,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k2_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1))) ) | (~spl2_1 | ~spl2_23)),
% 0.22/0.51    inference(resolution,[],[f198,f60])).
% 0.22/0.51  fof(f198,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) ) | ~spl2_23),
% 0.22/0.51    inference(avatar_component_clause,[],[f197])).
% 0.22/0.51  fof(f233,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X2)) ) | ~spl2_27),
% 0.22/0.51    inference(avatar_component_clause,[],[f232])).
% 0.22/0.51  fof(f296,plain,(
% 0.22/0.51    spl2_35 | ~spl2_18 | ~spl2_33),
% 0.22/0.51    inference(avatar_split_clause,[],[f291,f283,f160,f294])).
% 0.22/0.51  fof(f160,plain,(
% 0.22/0.51    spl2_18 <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.22/0.51  fof(f283,plain,(
% 0.22/0.51    spl2_33 <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.22/0.51  fof(f291,plain,(
% 0.22/0.51    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X3),X2) = k7_relat_1(k6_relat_1(X2),X3)) ) | (~spl2_18 | ~spl2_33)),
% 0.22/0.51    inference(superposition,[],[f284,f161])).
% 0.22/0.51  fof(f161,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ) | ~spl2_18),
% 0.22/0.51    inference(avatar_component_clause,[],[f160])).
% 0.22/0.51  fof(f284,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) | ~spl2_33),
% 0.22/0.51    inference(avatar_component_clause,[],[f283])).
% 0.22/0.51  fof(f285,plain,(
% 0.22/0.51    spl2_33 | ~spl2_26 | ~spl2_32),
% 0.22/0.51    inference(avatar_split_clause,[],[f280,f276,f224,f283])).
% 0.22/0.51  fof(f224,plain,(
% 0.22/0.51    spl2_26 <=> ! [X5,X7,X6] : k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) = k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.22/0.51  fof(f276,plain,(
% 0.22/0.51    spl2_32 <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.22/0.51  fof(f280,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_26 | ~spl2_32)),
% 0.22/0.51    inference(superposition,[],[f225,f277])).
% 0.22/0.51  fof(f277,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) ) | ~spl2_32),
% 0.22/0.51    inference(avatar_component_clause,[],[f276])).
% 0.22/0.51  fof(f225,plain,(
% 0.22/0.51    ( ! [X6,X7,X5] : (k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) = k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6)) ) | ~spl2_26),
% 0.22/0.51    inference(avatar_component_clause,[],[f224])).
% 0.22/0.51  fof(f278,plain,(
% 0.22/0.51    spl2_32 | ~spl2_12 | ~spl2_13 | ~spl2_28),
% 0.22/0.51    inference(avatar_split_clause,[],[f253,f247,f121,f117,f276])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    spl2_12 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    spl2_13 <=> ! [X1,X2] : v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.51  fof(f247,plain,(
% 0.22/0.51    spl2_28 <=> ! [X1,X0] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.22/0.51  fof(f253,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) ) | (~spl2_12 | ~spl2_13 | ~spl2_28)),
% 0.22/0.51    inference(subsumption_resolution,[],[f250,f122])).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) ) | ~spl2_13),
% 0.22/0.51    inference(avatar_component_clause,[],[f121])).
% 0.22/0.51  fof(f250,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) | ~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_12 | ~spl2_28)),
% 0.22/0.51    inference(resolution,[],[f248,f118])).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) ) | ~spl2_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f117])).
% 0.22/0.51  fof(f248,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) ) | ~spl2_28),
% 0.22/0.51    inference(avatar_component_clause,[],[f247])).
% 0.22/0.51  fof(f274,plain,(
% 0.22/0.51    ~spl2_31 | ~spl2_1 | ~spl2_2 | spl2_10 | ~spl2_23),
% 0.22/0.51    inference(avatar_split_clause,[],[f240,f197,f103,f63,f59,f271])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    spl2_10 <=> k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) = k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.51  fof(f240,plain,(
% 0.22/0.51    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) | (~spl2_1 | ~spl2_2 | spl2_10 | ~spl2_23)),
% 0.22/0.51    inference(backward_demodulation,[],[f105,f239])).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) | spl2_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f103])).
% 0.22/0.51  fof(f249,plain,(
% 0.22/0.51    spl2_28 | ~spl2_1 | ~spl2_2 | ~spl2_6 | ~spl2_23),
% 0.22/0.51    inference(avatar_split_clause,[],[f243,f197,f79,f63,f59,f247])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    spl2_6 <=> ! [X1,X0] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.51  fof(f243,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) ) | (~spl2_1 | ~spl2_2 | ~spl2_6 | ~spl2_23)),
% 0.22/0.51    inference(backward_demodulation,[],[f80,f239])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) ) | ~spl2_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f79])).
% 0.22/0.51  fof(f234,plain,(
% 0.22/0.51    spl2_27),
% 0.22/0.51    inference(avatar_split_clause,[],[f57,f232])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f51,f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f43,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f44,f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.22/0.51  fof(f226,plain,(
% 0.22/0.51    spl2_26 | ~spl2_1 | ~spl2_4 | ~spl2_9 | ~spl2_11 | ~spl2_13 | ~spl2_17 | ~spl2_22),
% 0.22/0.51    inference(avatar_split_clause,[],[f207,f193,f147,f121,f108,f96,f71,f59,f224])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    spl2_4 <=> ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    spl2_9 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    spl2_11 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    spl2_17 <=> ! [X1,X0] : (k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.51  fof(f193,plain,(
% 0.22/0.51    spl2_22 <=> ! [X1,X0,X2] : (~v1_relat_1(X0) | k7_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.22/0.51  fof(f207,plain,(
% 0.22/0.51    ( ! [X6,X7,X5] : (k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) = k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6)) ) | (~spl2_1 | ~spl2_4 | ~spl2_9 | ~spl2_11 | ~spl2_13 | ~spl2_17 | ~spl2_22)),
% 0.22/0.51    inference(backward_demodulation,[],[f158,f204])).
% 0.22/0.51  fof(f204,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1))) ) | (~spl2_1 | ~spl2_11 | ~spl2_22)),
% 0.22/0.51    inference(forward_demodulation,[],[f200,f109])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f108])).
% 0.22/0.51  fof(f200,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1))) ) | (~spl2_1 | ~spl2_22)),
% 0.22/0.51    inference(resolution,[],[f194,f60])).
% 0.22/0.51  fof(f194,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k7_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0)) ) | ~spl2_22),
% 0.22/0.51    inference(avatar_component_clause,[],[f193])).
% 0.22/0.51  fof(f158,plain,(
% 0.22/0.51    ( ! [X6,X7,X5] : (k5_relat_1(k7_relat_1(k6_relat_1(X7),X6),k6_relat_1(X5)) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5))) ) | (~spl2_1 | ~spl2_4 | ~spl2_9 | ~spl2_11 | ~spl2_13 | ~spl2_17)),
% 0.22/0.51    inference(forward_demodulation,[],[f157,f124])).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_9 | ~spl2_13)),
% 0.22/0.51    inference(resolution,[],[f122,f97])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f96])).
% 0.22/0.51  fof(f157,plain,(
% 0.22/0.51    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k7_relat_1(k6_relat_1(X7),X6),k6_relat_1(X5))) ) | (~spl2_1 | ~spl2_4 | ~spl2_11 | ~spl2_13 | ~spl2_17)),
% 0.22/0.51    inference(forward_demodulation,[],[f152,f155])).
% 0.22/0.51  fof(f155,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ) | (~spl2_1 | ~spl2_4 | ~spl2_11 | ~spl2_17)),
% 0.22/0.51    inference(forward_demodulation,[],[f154,f109])).
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ) | (~spl2_1 | ~spl2_4 | ~spl2_11 | ~spl2_17)),
% 0.22/0.51    inference(forward_demodulation,[],[f153,f109])).
% 0.22/0.51  fof(f153,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) ) | (~spl2_1 | ~spl2_4 | ~spl2_17)),
% 0.22/0.51    inference(forward_demodulation,[],[f150,f72])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) ) | ~spl2_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f71])).
% 0.22/0.51  fof(f150,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X0))) ) | (~spl2_1 | ~spl2_17)),
% 0.22/0.51    inference(resolution,[],[f148,f60])).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))) ) | ~spl2_17),
% 0.22/0.51    inference(avatar_component_clause,[],[f147])).
% 0.22/0.51  fof(f152,plain,(
% 0.22/0.51    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X6),X7)),k6_relat_1(X5))) ) | (~spl2_13 | ~spl2_17)),
% 0.22/0.51    inference(resolution,[],[f148,f122])).
% 0.22/0.51  fof(f220,plain,(
% 0.22/0.51    spl2_25 | ~spl2_11 | ~spl2_14 | ~spl2_24),
% 0.22/0.51    inference(avatar_split_clause,[],[f216,f211,f127,f108,f218])).
% 0.22/0.51  fof(f211,plain,(
% 0.22/0.51    spl2_24 <=> ! [X1,X0,X2] : k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.22/0.51  fof(f216,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)) ) | (~spl2_11 | ~spl2_14 | ~spl2_24)),
% 0.22/0.51    inference(forward_demodulation,[],[f214,f109])).
% 0.22/0.51  fof(f214,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)) ) | (~spl2_14 | ~spl2_24)),
% 0.22/0.51    inference(superposition,[],[f212,f128])).
% 0.22/0.51  fof(f212,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1))) ) | ~spl2_24),
% 0.22/0.51    inference(avatar_component_clause,[],[f211])).
% 0.22/0.51  fof(f213,plain,(
% 0.22/0.51    spl2_24 | ~spl2_1 | ~spl2_11 | ~spl2_22),
% 0.22/0.51    inference(avatar_split_clause,[],[f204,f193,f108,f59,f211])).
% 0.22/0.51  fof(f199,plain,(
% 0.22/0.51    spl2_23),
% 0.22/0.51    inference(avatar_split_clause,[],[f56,f197])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f46,f53])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.22/0.51  fof(f195,plain,(
% 0.22/0.51    spl2_22 | ~spl2_1 | ~spl2_21),
% 0.22/0.51    inference(avatar_split_clause,[],[f188,f185,f59,f193])).
% 0.22/0.51  fof(f185,plain,(
% 0.22/0.51    spl2_21 <=> ! [X1,X0,X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.22/0.51  fof(f188,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k7_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0)) ) | (~spl2_1 | ~spl2_21)),
% 0.22/0.51    inference(resolution,[],[f186,f60])).
% 0.22/0.51  fof(f186,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)) ) | ~spl2_21),
% 0.22/0.51    inference(avatar_component_clause,[],[f185])).
% 0.22/0.51  fof(f187,plain,(
% 0.22/0.51    spl2_21),
% 0.22/0.51    inference(avatar_split_clause,[],[f48,f185])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).
% 0.22/0.51  fof(f162,plain,(
% 0.22/0.51    spl2_18 | ~spl2_1 | ~spl2_4 | ~spl2_11 | ~spl2_17),
% 0.22/0.51    inference(avatar_split_clause,[],[f155,f147,f108,f71,f59,f160])).
% 0.22/0.51  fof(f149,plain,(
% 0.22/0.51    spl2_17 | ~spl2_1 | ~spl2_4 | ~spl2_16),
% 0.22/0.51    inference(avatar_split_clause,[],[f145,f139,f71,f59,f147])).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    spl2_16 <=> ! [X1,X0] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1)) | ~v1_relat_1(X0)) ) | (~spl2_1 | ~spl2_4 | ~spl2_16)),
% 0.22/0.51    inference(forward_demodulation,[],[f142,f72])).
% 0.22/0.51  fof(f142,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k6_relat_1(X1)))) ) | (~spl2_1 | ~spl2_16)),
% 0.22/0.51    inference(resolution,[],[f140,f60])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) ) | ~spl2_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f139])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    spl2_16),
% 0.22/0.51    inference(avatar_split_clause,[],[f40,f139])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    spl2_14 | ~spl2_8 | ~spl2_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f111,f108,f90,f127])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    spl2_8 <=> ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) ) | (~spl2_8 | ~spl2_11)),
% 0.22/0.51    inference(superposition,[],[f109,f91])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) ) | ~spl2_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f90])).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    spl2_13 | ~spl2_1 | ~spl2_5 | ~spl2_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f115,f108,f75,f59,f121])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    spl2_5 <=> ! [X1,X0] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) ) | (~spl2_1 | ~spl2_5 | ~spl2_11)),
% 0.22/0.51    inference(subsumption_resolution,[],[f114,f60])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) | ~v1_relat_1(k6_relat_1(X1))) ) | (~spl2_1 | ~spl2_5 | ~spl2_11)),
% 0.22/0.51    inference(subsumption_resolution,[],[f113,f60])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X1))) ) | (~spl2_5 | ~spl2_11)),
% 0.22/0.51    inference(superposition,[],[f76,f109])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f75])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    spl2_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f47,f117])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    spl2_11 | ~spl2_1 | ~spl2_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f99,f96,f59,f108])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_1 | ~spl2_9)),
% 0.22/0.51    inference(resolution,[],[f97,f60])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    ~spl2_10 | ~spl2_1 | ~spl2_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f101,f96,f59,f103])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) | (~spl2_1 | ~spl2_9)),
% 0.22/0.51    inference(backward_demodulation,[],[f54,f99])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 0.22/0.51    inference(definition_unfolding,[],[f34,f53])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.51    inference(negated_conjecture,[],[f17])).
% 0.22/0.51  fof(f17,conjecture,(
% 0.22/0.51    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    spl2_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f45,f96])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    spl2_8 | ~spl2_1 | ~spl2_3 | ~spl2_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f88,f83,f67,f59,f90])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    spl2_3 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    spl2_7 <=> ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.51  % (12245)Refutation not found, incomplete strategy% (12245)------------------------------
% 0.22/0.51  % (12245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12245)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) ) | (~spl2_1 | ~spl2_3 | ~spl2_7)),
% 0.22/0.51    inference(forward_demodulation,[],[f86,f68])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f67])).
% 0.22/0.51  % (12245)Memory used [KB]: 10618
% 0.22/0.51  % (12245)Time elapsed: 0.092 s
% 0.22/0.51  % (12245)------------------------------
% 0.22/0.51  % (12245)------------------------------
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0))))) ) | (~spl2_1 | ~spl2_7)),
% 0.22/0.51    inference(resolution,[],[f84,f60])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) ) | ~spl2_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f83])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    spl2_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f39,f83])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    spl2_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f55,f79])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f42,f53])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    spl2_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f49,f75])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    spl2_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f35,f71])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    spl2_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f38,f67])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    spl2_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f37,f63])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    spl2_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f36,f59])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f16])).
% 0.22/0.51  fof(f16,axiom,(
% 0.22/0.51    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (12241)------------------------------
% 0.22/0.51  % (12241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12241)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (12241)Memory used [KB]: 6780
% 0.22/0.51  % (12241)Time elapsed: 0.034 s
% 0.22/0.51  % (12241)------------------------------
% 0.22/0.51  % (12241)------------------------------
% 0.22/0.51  % (12233)Success in time 0.15 s
%------------------------------------------------------------------------------
