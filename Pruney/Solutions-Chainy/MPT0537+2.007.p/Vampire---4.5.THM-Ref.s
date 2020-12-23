%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 225 expanded)
%              Number of leaves         :   38 (  93 expanded)
%              Depth                    :   10
%              Number of atoms          :  271 ( 427 expanded)
%              Number of equality atoms :   59 ( 135 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f727,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f74,f79,f83,f87,f91,f105,f115,f121,f125,f129,f148,f153,f163,f177,f183,f455,f719,f726])).

fof(f726,plain,
    ( spl3_3
    | ~ spl3_12
    | ~ spl3_22
    | ~ spl3_57 ),
    inference(avatar_contradiction_clause,[],[f725])).

fof(f725,plain,
    ( $false
    | spl3_3
    | ~ spl3_12
    | ~ spl3_22
    | ~ spl3_57 ),
    inference(subsumption_resolution,[],[f724,f78])).

fof(f78,plain,
    ( k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_3
  <=> k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f724,plain,
    ( k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0)
    | ~ spl3_12
    | ~ spl3_22
    | ~ spl3_57 ),
    inference(forward_demodulation,[],[f720,f120])).

fof(f120,plain,
    ( ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl3_12
  <=> ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f720,plain,
    ( k8_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_xboole_0))
    | ~ spl3_22
    | ~ spl3_57 ),
    inference(superposition,[],[f718,f182])).

fof(f182,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl3_22
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f718,plain,
    ( ! [X0] : k8_relat_1(X0,sK0) = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k2_zfmisc_1(k1_relat_1(sK0),X0)))
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f717])).

fof(f717,plain,
    ( spl3_57
  <=> ! [X0] : k8_relat_1(X0,sK0) = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k2_zfmisc_1(k1_relat_1(sK0),X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f719,plain,
    ( spl3_57
    | ~ spl3_1
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f666,f453,f67,f717])).

fof(f67,plain,
    ( spl3_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f453,plain,
    ( spl3_48
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f666,plain,
    ( ! [X0] : k8_relat_1(X0,sK0) = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k2_zfmisc_1(k1_relat_1(sK0),X0)))
    | ~ spl3_1
    | ~ spl3_48 ),
    inference(resolution,[],[f454,f69])).

fof(f69,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f454,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k8_relat_1(X0,X1) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X0))) )
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f453])).

fof(f455,plain,(
    spl3_48 ),
    inference(avatar_split_clause,[],[f65,f453])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f46,f60])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f52,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).

fof(f183,plain,
    ( spl3_22
    | ~ spl3_4
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f178,f175,f81,f181])).

fof(f81,plain,
    ( spl3_4
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f175,plain,
    ( spl3_21
  <=> ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f178,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_21 ),
    inference(resolution,[],[f176,f82])).

fof(f82,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f176,plain,
    ( ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f175])).

fof(f177,plain,
    ( spl3_21
    | ~ spl3_2
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f168,f161,f72,f175])).

fof(f72,plain,
    ( spl3_2
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f161,plain,
    ( spl3_19
  <=> ! [X1,X0] :
        ( v1_xboole_0(k2_zfmisc_1(X0,X1))
        | ~ r1_xboole_0(X1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f168,plain,
    ( ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))
    | ~ spl3_2
    | ~ spl3_19 ),
    inference(resolution,[],[f162,f73])).

fof(f73,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X1,X1)
        | v1_xboole_0(k2_zfmisc_1(X0,X1)) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f161])).

fof(f163,plain,
    ( spl3_19
    | ~ spl3_11
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f156,f151,f113,f161])).

fof(f113,plain,
    ( spl3_11
  <=> ! [X1,X3,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f151,plain,
    ( spl3_18
  <=> ! [X0] :
        ( ~ r1_xboole_0(X0,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k2_zfmisc_1(X0,X1))
        | ~ r1_xboole_0(X1,X1) )
    | ~ spl3_11
    | ~ spl3_18 ),
    inference(resolution,[],[f152,f114])).

fof(f114,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_xboole_0(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X0))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f113])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,X0)
        | v1_xboole_0(X0) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f151])).

fof(f153,plain,
    ( spl3_18
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f149,f146,f85,f151])).

fof(f85,plain,
    ( spl3_5
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f146,plain,
    ( spl3_17
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X3,X2)
        | ~ r1_xboole_0(X2,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f149,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,X0)
        | v1_xboole_0(X0) )
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(resolution,[],[f147,f86])).

fof(f86,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | v1_xboole_0(X0) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f147,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,X2)
        | ~ r1_xboole_0(X2,X2) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f146])).

fof(f148,plain,
    ( spl3_17
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f132,f127,f123,f146])).

fof(f123,plain,
    ( spl3_13
  <=> ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f127,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f132,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,X2)
        | ~ r1_xboole_0(X2,X2) )
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(superposition,[],[f128,f124])).

fof(f124,plain,
    ( ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f123])).

fof(f128,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f127])).

fof(f129,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f63,f127])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f45,f60])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f125,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f62,f123])).

fof(f62,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f41,f60])).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f121,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f61,f119])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f38,f60])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f115,plain,
    ( spl3_11
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f107,f103,f89,f113])).

fof(f89,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f103,plain,
    ( spl3_9
  <=> ! [X1,X3,X0,X2] :
        ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        | ~ r1_xboole_0(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f107,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X0)) )
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(resolution,[],[f104,f90])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f104,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        | ~ r1_xboole_0(X2,X3) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f103])).

fof(f105,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f51,f103])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f91,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f47,f89])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f87,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f40,f85])).

fof(f40,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f83,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f39,f81])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f79,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f36,f76])).

fof(f36,plain,(
    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k8_relat_1(k1_xboole_0,X0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( k1_xboole_0 != k8_relat_1(k1_xboole_0,X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_relat_1)).

fof(f74,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f37,f72])).

fof(f37,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f70,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f35,f67])).

fof(f35,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:43:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (1234173953)
% 0.13/0.36  ipcrm: permission denied for id (1234206723)
% 0.13/0.37  ipcrm: permission denied for id (1234239493)
% 0.20/0.46  ipcrm: permission denied for id (1234468942)
% 0.20/0.47  ipcrm: permission denied for id (1234501717)
% 0.20/0.50  ipcrm: permission denied for id (1234567279)
% 0.20/0.50  ipcrm: permission denied for id (1234600049)
% 0.20/0.58  % (7309)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.60  % (7309)Refutation found. Thanks to Tanya!
% 0.20/0.60  % SZS status Theorem for theBenchmark
% 0.20/0.60  % SZS output start Proof for theBenchmark
% 0.20/0.60  fof(f727,plain,(
% 0.20/0.60    $false),
% 0.20/0.60    inference(avatar_sat_refutation,[],[f70,f74,f79,f83,f87,f91,f105,f115,f121,f125,f129,f148,f153,f163,f177,f183,f455,f719,f726])).
% 0.20/0.60  fof(f726,plain,(
% 0.20/0.60    spl3_3 | ~spl3_12 | ~spl3_22 | ~spl3_57),
% 0.20/0.60    inference(avatar_contradiction_clause,[],[f725])).
% 0.20/0.60  fof(f725,plain,(
% 0.20/0.60    $false | (spl3_3 | ~spl3_12 | ~spl3_22 | ~spl3_57)),
% 0.20/0.60    inference(subsumption_resolution,[],[f724,f78])).
% 0.20/0.60  fof(f78,plain,(
% 0.20/0.60    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) | spl3_3),
% 0.20/0.60    inference(avatar_component_clause,[],[f76])).
% 0.20/0.60  fof(f76,plain,(
% 0.20/0.60    spl3_3 <=> k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.60  fof(f724,plain,(
% 0.20/0.60    k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0) | (~spl3_12 | ~spl3_22 | ~spl3_57)),
% 0.20/0.60    inference(forward_demodulation,[],[f720,f120])).
% 0.20/0.60  fof(f120,plain,(
% 0.20/0.60    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) ) | ~spl3_12),
% 0.20/0.60    inference(avatar_component_clause,[],[f119])).
% 0.20/0.60  fof(f119,plain,(
% 0.20/0.60    spl3_12 <=> ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.60  fof(f720,plain,(
% 0.20/0.60    k8_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_xboole_0)) | (~spl3_22 | ~spl3_57)),
% 0.20/0.60    inference(superposition,[],[f718,f182])).
% 0.20/0.60  fof(f182,plain,(
% 0.20/0.60    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl3_22),
% 0.20/0.60    inference(avatar_component_clause,[],[f181])).
% 0.20/0.60  fof(f181,plain,(
% 0.20/0.60    spl3_22 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.60  fof(f718,plain,(
% 0.20/0.60    ( ! [X0] : (k8_relat_1(X0,sK0) = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k2_zfmisc_1(k1_relat_1(sK0),X0)))) ) | ~spl3_57),
% 0.20/0.60    inference(avatar_component_clause,[],[f717])).
% 0.20/0.60  fof(f717,plain,(
% 0.20/0.60    spl3_57 <=> ! [X0] : k8_relat_1(X0,sK0) = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k2_zfmisc_1(k1_relat_1(sK0),X0)))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.20/0.60  fof(f719,plain,(
% 0.20/0.60    spl3_57 | ~spl3_1 | ~spl3_48),
% 0.20/0.60    inference(avatar_split_clause,[],[f666,f453,f67,f717])).
% 0.20/0.60  fof(f67,plain,(
% 0.20/0.60    spl3_1 <=> v1_relat_1(sK0)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.60  fof(f453,plain,(
% 0.20/0.60    spl3_48 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.20/0.60  fof(f666,plain,(
% 0.20/0.60    ( ! [X0] : (k8_relat_1(X0,sK0) = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k2_zfmisc_1(k1_relat_1(sK0),X0)))) ) | (~spl3_1 | ~spl3_48)),
% 0.20/0.60    inference(resolution,[],[f454,f69])).
% 0.20/0.60  fof(f69,plain,(
% 0.20/0.60    v1_relat_1(sK0) | ~spl3_1),
% 0.20/0.60    inference(avatar_component_clause,[],[f67])).
% 0.20/0.60  fof(f454,plain,(
% 0.20/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X0)))) ) | ~spl3_48),
% 0.20/0.60    inference(avatar_component_clause,[],[f453])).
% 0.20/0.60  fof(f455,plain,(
% 0.20/0.60    spl3_48),
% 0.20/0.60    inference(avatar_split_clause,[],[f65,f453])).
% 0.20/0.60  fof(f65,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 0.20/0.60    inference(definition_unfolding,[],[f46,f60])).
% 0.20/0.60  fof(f60,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.60    inference(definition_unfolding,[],[f42,f59])).
% 0.20/0.60  fof(f59,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.60    inference(definition_unfolding,[],[f43,f58])).
% 0.20/0.60  fof(f58,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.60    inference(definition_unfolding,[],[f48,f57])).
% 0.20/0.60  fof(f57,plain,(
% 0.20/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.60    inference(definition_unfolding,[],[f49,f56])).
% 0.20/0.60  fof(f56,plain,(
% 0.20/0.60    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.60    inference(definition_unfolding,[],[f52,f55])).
% 0.20/0.60  fof(f55,plain,(
% 0.20/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.60    inference(definition_unfolding,[],[f53,f54])).
% 0.20/0.60  fof(f54,plain,(
% 0.20/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f13])).
% 0.20/0.60  fof(f13,axiom,(
% 0.20/0.60    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.60  fof(f53,plain,(
% 0.20/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f12])).
% 0.20/0.60  fof(f12,axiom,(
% 0.20/0.60    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.60  fof(f52,plain,(
% 0.20/0.60    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f11])).
% 0.20/0.60  fof(f11,axiom,(
% 0.20/0.60    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.60  fof(f49,plain,(
% 0.20/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f10])).
% 0.20/0.60  fof(f10,axiom,(
% 0.20/0.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.60  fof(f48,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f9])).
% 0.20/0.60  fof(f9,axiom,(
% 0.20/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.60  fof(f43,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f8])).
% 0.20/0.60  fof(f8,axiom,(
% 0.20/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.60  fof(f42,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.60    inference(cnf_transformation,[],[f15])).
% 0.20/0.60  fof(f15,axiom,(
% 0.20/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.60  fof(f46,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f26])).
% 0.20/0.60  fof(f26,plain,(
% 0.20/0.60    ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.60    inference(ennf_transformation,[],[f16])).
% 0.20/0.60  fof(f16,axiom,(
% 0.20/0.60    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).
% 0.20/0.60  fof(f183,plain,(
% 0.20/0.60    spl3_22 | ~spl3_4 | ~spl3_21),
% 0.20/0.60    inference(avatar_split_clause,[],[f178,f175,f81,f181])).
% 0.20/0.60  fof(f81,plain,(
% 0.20/0.60    spl3_4 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.60  fof(f175,plain,(
% 0.20/0.60    spl3_21 <=> ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.60  fof(f178,plain,(
% 0.20/0.60    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | (~spl3_4 | ~spl3_21)),
% 0.20/0.60    inference(resolution,[],[f176,f82])).
% 0.20/0.60  fof(f82,plain,(
% 0.20/0.60    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl3_4),
% 0.20/0.60    inference(avatar_component_clause,[],[f81])).
% 0.20/0.60  fof(f176,plain,(
% 0.20/0.60    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))) ) | ~spl3_21),
% 0.20/0.60    inference(avatar_component_clause,[],[f175])).
% 0.20/0.60  fof(f177,plain,(
% 0.20/0.60    spl3_21 | ~spl3_2 | ~spl3_19),
% 0.20/0.60    inference(avatar_split_clause,[],[f168,f161,f72,f175])).
% 0.20/0.60  fof(f72,plain,(
% 0.20/0.60    spl3_2 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.60  fof(f161,plain,(
% 0.20/0.60    spl3_19 <=> ! [X1,X0] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~r1_xboole_0(X1,X1))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.60  fof(f168,plain,(
% 0.20/0.60    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))) ) | (~spl3_2 | ~spl3_19)),
% 0.20/0.60    inference(resolution,[],[f162,f73])).
% 0.20/0.60  fof(f73,plain,(
% 0.20/0.60    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl3_2),
% 0.20/0.60    inference(avatar_component_clause,[],[f72])).
% 0.20/0.60  fof(f162,plain,(
% 0.20/0.60    ( ! [X0,X1] : (~r1_xboole_0(X1,X1) | v1_xboole_0(k2_zfmisc_1(X0,X1))) ) | ~spl3_19),
% 0.20/0.60    inference(avatar_component_clause,[],[f161])).
% 0.20/0.60  fof(f163,plain,(
% 0.20/0.60    spl3_19 | ~spl3_11 | ~spl3_18),
% 0.20/0.60    inference(avatar_split_clause,[],[f156,f151,f113,f161])).
% 0.20/0.60  fof(f113,plain,(
% 0.20/0.60    spl3_11 <=> ! [X1,X3,X0,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X0)))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.60  fof(f151,plain,(
% 0.20/0.60    spl3_18 <=> ! [X0] : (~r1_xboole_0(X0,X0) | v1_xboole_0(X0))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.60  fof(f156,plain,(
% 0.20/0.60    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~r1_xboole_0(X1,X1)) ) | (~spl3_11 | ~spl3_18)),
% 0.20/0.60    inference(resolution,[],[f152,f114])).
% 0.20/0.60  fof(f114,plain,(
% 0.20/0.60    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X0)) | ~r1_xboole_0(X0,X1)) ) | ~spl3_11),
% 0.20/0.60    inference(avatar_component_clause,[],[f113])).
% 0.20/0.60  fof(f152,plain,(
% 0.20/0.60    ( ! [X0] : (~r1_xboole_0(X0,X0) | v1_xboole_0(X0)) ) | ~spl3_18),
% 0.20/0.60    inference(avatar_component_clause,[],[f151])).
% 0.20/0.60  fof(f153,plain,(
% 0.20/0.60    spl3_18 | ~spl3_5 | ~spl3_17),
% 0.20/0.60    inference(avatar_split_clause,[],[f149,f146,f85,f151])).
% 0.20/0.60  fof(f85,plain,(
% 0.20/0.60    spl3_5 <=> ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK1(X0),X0))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.60  fof(f146,plain,(
% 0.20/0.60    spl3_17 <=> ! [X3,X2] : (~r2_hidden(X3,X2) | ~r1_xboole_0(X2,X2))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.60  fof(f149,plain,(
% 0.20/0.60    ( ! [X0] : (~r1_xboole_0(X0,X0) | v1_xboole_0(X0)) ) | (~spl3_5 | ~spl3_17)),
% 0.20/0.60    inference(resolution,[],[f147,f86])).
% 0.20/0.60  fof(f86,plain,(
% 0.20/0.60    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_xboole_0(X0)) ) | ~spl3_5),
% 0.20/0.60    inference(avatar_component_clause,[],[f85])).
% 0.20/0.60  fof(f147,plain,(
% 0.20/0.60    ( ! [X2,X3] : (~r2_hidden(X3,X2) | ~r1_xboole_0(X2,X2)) ) | ~spl3_17),
% 0.20/0.60    inference(avatar_component_clause,[],[f146])).
% 0.20/0.60  fof(f148,plain,(
% 0.20/0.60    spl3_17 | ~spl3_13 | ~spl3_14),
% 0.20/0.60    inference(avatar_split_clause,[],[f132,f127,f123,f146])).
% 0.20/0.60  fof(f123,plain,(
% 0.20/0.60    spl3_13 <=> ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.60  fof(f127,plain,(
% 0.20/0.60    spl3_14 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.60  fof(f132,plain,(
% 0.20/0.60    ( ! [X2,X3] : (~r2_hidden(X3,X2) | ~r1_xboole_0(X2,X2)) ) | (~spl3_13 | ~spl3_14)),
% 0.20/0.60    inference(superposition,[],[f128,f124])).
% 0.20/0.60  fof(f124,plain,(
% 0.20/0.60    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) ) | ~spl3_13),
% 0.20/0.60    inference(avatar_component_clause,[],[f123])).
% 0.20/0.60  fof(f128,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r1_xboole_0(X0,X1)) ) | ~spl3_14),
% 0.20/0.60    inference(avatar_component_clause,[],[f127])).
% 0.20/0.60  fof(f129,plain,(
% 0.20/0.60    spl3_14),
% 0.20/0.60    inference(avatar_split_clause,[],[f63,f127])).
% 0.20/0.60  fof(f63,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.20/0.60    inference(definition_unfolding,[],[f45,f60])).
% 0.20/0.60  fof(f45,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.20/0.60    inference(cnf_transformation,[],[f34])).
% 0.20/0.60  fof(f34,plain,(
% 0.20/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f33])).
% 0.20/0.60  fof(f33,plain,(
% 0.20/0.60    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.60    introduced(choice_axiom,[])).
% 0.20/0.60  fof(f25,plain,(
% 0.20/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.60    inference(ennf_transformation,[],[f20])).
% 0.20/0.60  fof(f20,plain,(
% 0.20/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.60    inference(rectify,[],[f5])).
% 0.20/0.60  fof(f5,axiom,(
% 0.20/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.60  fof(f125,plain,(
% 0.20/0.60    spl3_13),
% 0.20/0.60    inference(avatar_split_clause,[],[f62,f123])).
% 0.20/0.60  fof(f62,plain,(
% 0.20/0.60    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 0.20/0.60    inference(definition_unfolding,[],[f41,f60])).
% 0.20/0.60  fof(f41,plain,(
% 0.20/0.60    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.20/0.60    inference(cnf_transformation,[],[f19])).
% 0.20/0.60  fof(f19,plain,(
% 0.20/0.60    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.60    inference(rectify,[],[f2])).
% 0.20/0.60  fof(f2,axiom,(
% 0.20/0.60    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.20/0.60  fof(f121,plain,(
% 0.20/0.60    spl3_12),
% 0.20/0.60    inference(avatar_split_clause,[],[f61,f119])).
% 0.20/0.60  fof(f61,plain,(
% 0.20/0.60    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 0.20/0.60    inference(definition_unfolding,[],[f38,f60])).
% 0.20/0.60  fof(f38,plain,(
% 0.20/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f6])).
% 0.20/0.60  fof(f6,axiom,(
% 0.20/0.60    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.60  fof(f115,plain,(
% 0.20/0.60    spl3_11 | ~spl3_6 | ~spl3_9),
% 0.20/0.60    inference(avatar_split_clause,[],[f107,f103,f89,f113])).
% 0.20/0.60  fof(f89,plain,(
% 0.20/0.60    spl3_6 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.60  fof(f103,plain,(
% 0.20/0.60    spl3_9 <=> ! [X1,X3,X0,X2] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X2,X3))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.60  fof(f107,plain,(
% 0.20/0.60    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X0))) ) | (~spl3_6 | ~spl3_9)),
% 0.20/0.60    inference(resolution,[],[f104,f90])).
% 0.20/0.60  fof(f90,plain,(
% 0.20/0.60    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl3_6),
% 0.20/0.60    inference(avatar_component_clause,[],[f89])).
% 0.20/0.60  fof(f104,plain,(
% 0.20/0.60    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X2,X3)) ) | ~spl3_9),
% 0.20/0.60    inference(avatar_component_clause,[],[f103])).
% 0.20/0.60  fof(f105,plain,(
% 0.20/0.60    spl3_9),
% 0.20/0.60    inference(avatar_split_clause,[],[f51,f103])).
% 0.20/0.60  fof(f51,plain,(
% 0.20/0.60    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X2,X3)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f28])).
% 0.20/0.60  fof(f28,plain,(
% 0.20/0.60    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.60    inference(ennf_transformation,[],[f14])).
% 0.20/0.60  fof(f14,axiom,(
% 0.20/0.60    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 0.20/0.60  fof(f91,plain,(
% 0.20/0.60    spl3_6),
% 0.20/0.60    inference(avatar_split_clause,[],[f47,f89])).
% 0.20/0.60  fof(f47,plain,(
% 0.20/0.60    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f27])).
% 0.20/0.60  fof(f27,plain,(
% 0.20/0.60    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.60    inference(ennf_transformation,[],[f4])).
% 0.20/0.60  fof(f4,axiom,(
% 0.20/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.60  fof(f87,plain,(
% 0.20/0.60    spl3_5),
% 0.20/0.60    inference(avatar_split_clause,[],[f40,f85])).
% 0.20/0.60  fof(f40,plain,(
% 0.20/0.60    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f32])).
% 0.20/0.60  fof(f32,plain,(
% 0.20/0.60    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK1(X0),X0))),
% 0.20/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f31])).
% 0.20/0.60  fof(f31,plain,(
% 0.20/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.20/0.60    introduced(choice_axiom,[])).
% 0.20/0.60  fof(f24,plain,(
% 0.20/0.60    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 0.20/0.60    inference(ennf_transformation,[],[f21])).
% 0.20/0.60  fof(f21,plain,(
% 0.20/0.60    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 0.20/0.60    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.60  fof(f1,axiom,(
% 0.20/0.60    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.60  fof(f83,plain,(
% 0.20/0.60    spl3_4),
% 0.20/0.60    inference(avatar_split_clause,[],[f39,f81])).
% 0.20/0.60  fof(f39,plain,(
% 0.20/0.60    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f23])).
% 0.20/0.60  fof(f23,plain,(
% 0.20/0.60    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.60    inference(ennf_transformation,[],[f3])).
% 0.20/0.60  fof(f3,axiom,(
% 0.20/0.60    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.60  fof(f79,plain,(
% 0.20/0.60    ~spl3_3),
% 0.20/0.60    inference(avatar_split_clause,[],[f36,f76])).
% 0.20/0.60  fof(f36,plain,(
% 0.20/0.60    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)),
% 0.20/0.60    inference(cnf_transformation,[],[f30])).
% 0.20/0.60  fof(f30,plain,(
% 0.20/0.60    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) & v1_relat_1(sK0)),
% 0.20/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f29])).
% 0.20/0.60  fof(f29,plain,(
% 0.20/0.60    ? [X0] : (k1_xboole_0 != k8_relat_1(k1_xboole_0,X0) & v1_relat_1(X0)) => (k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) & v1_relat_1(sK0))),
% 0.20/0.60    introduced(choice_axiom,[])).
% 0.20/0.60  fof(f22,plain,(
% 0.20/0.60    ? [X0] : (k1_xboole_0 != k8_relat_1(k1_xboole_0,X0) & v1_relat_1(X0))),
% 0.20/0.60    inference(ennf_transformation,[],[f18])).
% 0.20/0.60  fof(f18,negated_conjecture,(
% 0.20/0.60    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.20/0.60    inference(negated_conjecture,[],[f17])).
% 0.20/0.60  fof(f17,conjecture,(
% 0.20/0.60    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_relat_1)).
% 0.20/0.60  fof(f74,plain,(
% 0.20/0.60    spl3_2),
% 0.20/0.60    inference(avatar_split_clause,[],[f37,f72])).
% 0.20/0.60  fof(f37,plain,(
% 0.20/0.60    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f7])).
% 0.20/0.60  fof(f7,axiom,(
% 0.20/0.60    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.60  fof(f70,plain,(
% 0.20/0.60    spl3_1),
% 0.20/0.60    inference(avatar_split_clause,[],[f35,f67])).
% 0.20/0.60  fof(f35,plain,(
% 0.20/0.60    v1_relat_1(sK0)),
% 0.20/0.60    inference(cnf_transformation,[],[f30])).
% 0.20/0.60  % SZS output end Proof for theBenchmark
% 0.20/0.60  % (7309)------------------------------
% 0.20/0.60  % (7309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.60  % (7309)Termination reason: Refutation
% 0.20/0.60  
% 0.20/0.60  % (7309)Memory used [KB]: 6524
% 0.20/0.60  % (7309)Time elapsed: 0.013 s
% 0.20/0.60  % (7309)------------------------------
% 0.20/0.60  % (7309)------------------------------
% 0.20/0.60  % (7137)Success in time 0.245 s
%------------------------------------------------------------------------------
