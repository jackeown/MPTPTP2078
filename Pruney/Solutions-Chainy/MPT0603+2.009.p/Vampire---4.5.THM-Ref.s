%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 190 expanded)
%              Number of leaves         :   34 (  81 expanded)
%              Depth                    :   10
%              Number of atoms          :  283 ( 446 expanded)
%              Number of equality atoms :   55 ( 102 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f345,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f74,f83,f87,f92,f97,f102,f111,f117,f130,f199,f233,f239,f262,f302,f338,f343])).

fof(f343,plain,
    ( spl5_5
    | ~ spl5_13
    | ~ spl5_28
    | ~ spl5_37 ),
    inference(avatar_contradiction_clause,[],[f342])).

fof(f342,plain,
    ( $false
    | spl5_5
    | ~ spl5_13
    | ~ spl5_28
    | ~ spl5_37 ),
    inference(subsumption_resolution,[],[f341,f82])).

fof(f82,plain,
    ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl5_5
  <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f341,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    | ~ spl5_13
    | ~ spl5_28
    | ~ spl5_37 ),
    inference(forward_demodulation,[],[f339,f129])).

fof(f129,plain,
    ( k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl5_13
  <=> k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f339,plain,
    ( k7_relat_1(k7_relat_1(sK2,sK0),sK1) = k7_relat_1(sK2,k1_xboole_0)
    | ~ spl5_28
    | ~ spl5_37 ),
    inference(superposition,[],[f337,f261])).

fof(f261,plain,
    ( k1_xboole_0 = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl5_28
  <=> k1_xboole_0 = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f337,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f336])).

fof(f336,plain,
    ( spl5_37
  <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f338,plain,
    ( spl5_37
    | ~ spl5_1
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f332,f300,f61,f336])).

fof(f61,plain,
    ( spl5_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f300,plain,
    ( spl5_33
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f332,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
    | ~ spl5_1
    | ~ spl5_33 ),
    inference(resolution,[],[f301,f63])).

fof(f63,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f301,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f300])).

fof(f302,plain,(
    spl5_33 ),
    inference(avatar_split_clause,[],[f59,f300])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f46,f56])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f48,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f262,plain,
    ( spl5_28
    | ~ spl5_8
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f241,f236,f95,f259])).

fof(f95,plain,
    ( spl5_8
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f236,plain,
    ( spl5_27
  <=> v1_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f241,plain,
    ( k1_xboole_0 = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_8
    | ~ spl5_27 ),
    inference(resolution,[],[f238,f96])).

fof(f96,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f238,plain,
    ( v1_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f236])).

fof(f239,plain,
    ( spl5_27
    | ~ spl5_3
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f234,f231,f71,f236])).

fof(f71,plain,
    ( spl5_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f231,plain,
    ( spl5_26
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(X0,X1)
        | v1_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f234,plain,
    ( v1_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ spl5_3
    | ~ spl5_26 ),
    inference(resolution,[],[f232,f73])).

fof(f73,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f232,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | v1_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f231])).

fof(f233,plain,
    ( spl5_26
    | ~ spl5_6
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f229,f197,f85,f231])).

fof(f85,plain,
    ( spl5_6
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

% (29075)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
fof(f197,plain,
    ( spl5_23
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f229,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | v1_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )
    | ~ spl5_6
    | ~ spl5_23 ),
    inference(resolution,[],[f198,f86])).

fof(f86,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0),X0)
        | v1_xboole_0(X0) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f198,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f197])).

fof(f199,plain,(
    spl5_23 ),
    inference(avatar_split_clause,[],[f57,f197])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f41,f56])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f30])).

% (29072)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f130,plain,
    ( spl5_13
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f120,f114,f95,f127])).

fof(f114,plain,
    ( spl5_12
  <=> v1_xboole_0(k7_relat_1(sK2,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

% (29084)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
fof(f120,plain,
    ( k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0)
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(resolution,[],[f116,f96])).

fof(f116,plain,
    ( v1_xboole_0(k7_relat_1(sK2,k1_xboole_0))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f114])).

fof(f117,plain,
    ( spl5_12
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f112,f109,f66,f114])).

fof(f66,plain,
    ( spl5_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f109,plain,
    ( spl5_11
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v1_xboole_0(k7_relat_1(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f112,plain,
    ( v1_xboole_0(k7_relat_1(sK2,k1_xboole_0))
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(resolution,[],[f110,f68])).

fof(f68,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v1_xboole_0(k7_relat_1(sK2,X0)) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f109])).

fof(f111,plain,
    ( spl5_11
    | ~ spl5_1
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f107,f100,f61,f109])).

fof(f100,plain,
    ( spl5_9
  <=> ! [X1,X0] :
        ( v1_xboole_0(k7_relat_1(X0,X1))
        | ~ v1_xboole_0(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v1_xboole_0(k7_relat_1(sK2,X0)) )
    | ~ spl5_1
    | ~ spl5_9 ),
    inference(resolution,[],[f101,f63])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_xboole_0(X1)
        | v1_xboole_0(k7_relat_1(X0,X1)) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f102,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f42,f100])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k7_relat_1(X0,X1))
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & v1_relat_1(X0) )
     => ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_relat_1)).

fof(f97,plain,
    ( spl5_8
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f93,f90,f66,f95])).

fof(f90,plain,
    ( spl5_7
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X1)
        | X0 = X1
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f93,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(resolution,[],[f91,f68])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | X0 = X1
        | ~ v1_xboole_0(X1) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f92,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f44,f90])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f87,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f37,f85])).

fof(f37,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f83,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f34,f80])).

fof(f34,plain,(
    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    & r1_xboole_0(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
        & r1_xboole_0(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
      & r1_xboole_0(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_xboole_0(X0,X1)
         => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

fof(f74,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f33,f71])).

fof(f33,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f35,f66])).

fof(f35,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f64,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f32,f61])).

fof(f32,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:27:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (29073)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (29087)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.47  % (29077)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (29080)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (29086)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (29076)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (29085)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (29079)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (29071)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (29077)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f345,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f64,f69,f74,f83,f87,f92,f97,f102,f111,f117,f130,f199,f233,f239,f262,f302,f338,f343])).
% 0.21/0.48  fof(f343,plain,(
% 0.21/0.48    spl5_5 | ~spl5_13 | ~spl5_28 | ~spl5_37),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f342])).
% 0.21/0.48  fof(f342,plain,(
% 0.21/0.48    $false | (spl5_5 | ~spl5_13 | ~spl5_28 | ~spl5_37)),
% 0.21/0.48    inference(subsumption_resolution,[],[f341,f82])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) | spl5_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl5_5 <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.48  fof(f341,plain,(
% 0.21/0.48    k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1) | (~spl5_13 | ~spl5_28 | ~spl5_37)),
% 0.21/0.48    inference(forward_demodulation,[],[f339,f129])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0) | ~spl5_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f127])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    spl5_13 <=> k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.48  fof(f339,plain,(
% 0.21/0.48    k7_relat_1(k7_relat_1(sK2,sK0),sK1) = k7_relat_1(sK2,k1_xboole_0) | (~spl5_28 | ~spl5_37)),
% 0.21/0.48    inference(superposition,[],[f337,f261])).
% 0.21/0.48  fof(f261,plain,(
% 0.21/0.48    k1_xboole_0 = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl5_28),
% 0.21/0.48    inference(avatar_component_clause,[],[f259])).
% 0.21/0.48  fof(f259,plain,(
% 0.21/0.48    spl5_28 <=> k1_xboole_0 = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.21/0.48  fof(f337,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ) | ~spl5_37),
% 0.21/0.48    inference(avatar_component_clause,[],[f336])).
% 0.21/0.48  fof(f336,plain,(
% 0.21/0.48    spl5_37 <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.21/0.48  fof(f338,plain,(
% 0.21/0.48    spl5_37 | ~spl5_1 | ~spl5_33),
% 0.21/0.48    inference(avatar_split_clause,[],[f332,f300,f61,f336])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl5_1 <=> v1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.48  fof(f300,plain,(
% 0.21/0.48    spl5_33 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~v1_relat_1(X2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.21/0.48  fof(f332,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ) | (~spl5_1 | ~spl5_33)),
% 0.21/0.48    inference(resolution,[],[f301,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    v1_relat_1(sK2) | ~spl5_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f61])).
% 0.21/0.48  fof(f301,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ) | ~spl5_33),
% 0.21/0.48    inference(avatar_component_clause,[],[f300])).
% 0.21/0.48  fof(f302,plain,(
% 0.21/0.48    spl5_33),
% 0.21/0.48    inference(avatar_split_clause,[],[f59,f300])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f46,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f38,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f39,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f45,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f47,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f48,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f49,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.21/0.48  fof(f262,plain,(
% 0.21/0.48    spl5_28 | ~spl5_8 | ~spl5_27),
% 0.21/0.48    inference(avatar_split_clause,[],[f241,f236,f95,f259])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl5_8 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.48  fof(f236,plain,(
% 0.21/0.48    spl5_27 <=> v1_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.48  fof(f241,plain,(
% 0.21/0.48    k1_xboole_0 = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | (~spl5_8 | ~spl5_27)),
% 0.21/0.48    inference(resolution,[],[f238,f96])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl5_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f95])).
% 0.21/0.48  fof(f238,plain,(
% 0.21/0.48    v1_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | ~spl5_27),
% 0.21/0.48    inference(avatar_component_clause,[],[f236])).
% 0.21/0.48  fof(f239,plain,(
% 0.21/0.48    spl5_27 | ~spl5_3 | ~spl5_26),
% 0.21/0.48    inference(avatar_split_clause,[],[f234,f231,f71,f236])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl5_3 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.48  fof(f231,plain,(
% 0.21/0.48    spl5_26 <=> ! [X1,X0] : (~r1_xboole_0(X0,X1) | v1_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.48  fof(f234,plain,(
% 0.21/0.48    v1_xboole_0(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | (~spl5_3 | ~spl5_26)),
% 0.21/0.48    inference(resolution,[],[f232,f73])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    r1_xboole_0(sK0,sK1) | ~spl5_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f71])).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | v1_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ) | ~spl5_26),
% 0.21/0.48    inference(avatar_component_clause,[],[f231])).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    spl5_26 | ~spl5_6 | ~spl5_23),
% 0.21/0.48    inference(avatar_split_clause,[],[f229,f197,f85,f231])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl5_6 <=> ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.48  % (29075)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  fof(f197,plain,(
% 0.21/0.48    spl5_23 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.48  fof(f229,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | v1_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ) | (~spl5_6 | ~spl5_23)),
% 0.21/0.48    inference(resolution,[],[f198,f86])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) ) | ~spl5_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f85])).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r1_xboole_0(X0,X1)) ) | ~spl5_23),
% 0.21/0.48    inference(avatar_component_clause,[],[f197])).
% 0.21/0.48  fof(f199,plain,(
% 0.21/0.48    spl5_23),
% 0.21/0.48    inference(avatar_split_clause,[],[f57,f197])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f41,f56])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f30])).
% 0.21/0.48  % (29072)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(rectify,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    spl5_13 | ~spl5_8 | ~spl5_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f120,f114,f95,f127])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    spl5_12 <=> v1_xboole_0(k7_relat_1(sK2,k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.48  % (29084)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0) | (~spl5_8 | ~spl5_12)),
% 0.21/0.48    inference(resolution,[],[f116,f96])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    v1_xboole_0(k7_relat_1(sK2,k1_xboole_0)) | ~spl5_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f114])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    spl5_12 | ~spl5_2 | ~spl5_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f112,f109,f66,f114])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl5_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    spl5_11 <=> ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k7_relat_1(sK2,X0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    v1_xboole_0(k7_relat_1(sK2,k1_xboole_0)) | (~spl5_2 | ~spl5_11)),
% 0.21/0.48    inference(resolution,[],[f110,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0) | ~spl5_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f66])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k7_relat_1(sK2,X0))) ) | ~spl5_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f109])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    spl5_11 | ~spl5_1 | ~spl5_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f107,f100,f61,f109])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    spl5_9 <=> ! [X1,X0] : (v1_xboole_0(k7_relat_1(X0,X1)) | ~v1_xboole_0(X1) | ~v1_relat_1(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k7_relat_1(sK2,X0))) ) | (~spl5_1 | ~spl5_9)),
% 0.21/0.48    inference(resolution,[],[f101,f63])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_xboole_0(X1) | v1_xboole_0(k7_relat_1(X0,X1))) ) | ~spl5_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f100])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    spl5_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f42,f100])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_xboole_0(k7_relat_1(X0,X1)) | ~v1_xboole_0(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | ~v1_xboole_0(X1) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | (~v1_xboole_0(X1) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_xboole_0(X1) & v1_relat_1(X0)) => (v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_relat_1)).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    spl5_8 | ~spl5_2 | ~spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f93,f90,f66,f95])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    spl5_7 <=> ! [X1,X0] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) ) | (~spl5_2 | ~spl5_7)),
% 0.21/0.48    inference(resolution,[],[f91,f68])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) ) | ~spl5_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f90])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f44,f90])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    spl5_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f37,f85])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.48    inference(rectify,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ~spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f34,f80])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) & r1_xboole_0(sK0,sK1) & v1_relat_1(sK2)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1) & v1_relat_1(X2)) => (k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) & r1_xboole_0(sK0,sK1) & v1_relat_1(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1) & v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1)) & v1_relat_1(X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.21/0.48    inference(negated_conjecture,[],[f14])).
% 0.21/0.48  fof(f14,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    spl5_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f33,f71])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    r1_xboole_0(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    spl5_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f35,f66])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f61])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    v1_relat_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (29077)------------------------------
% 0.21/0.48  % (29077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (29077)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (29077)Memory used [KB]: 6268
% 0.21/0.48  % (29077)Time elapsed: 0.015 s
% 0.21/0.48  % (29077)------------------------------
% 0.21/0.48  % (29077)------------------------------
% 0.21/0.49  % (29082)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (29074)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (29069)Success in time 0.128 s
%------------------------------------------------------------------------------
