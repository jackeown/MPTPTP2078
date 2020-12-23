%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:04 EST 2020

% Result     : Theorem 2.17s
% Output     : Refutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 261 expanded)
%              Number of leaves         :   32 ( 114 expanded)
%              Depth                    :    8
%              Number of atoms          :  296 ( 533 expanded)
%              Number of equality atoms :   90 ( 191 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2755,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f74,f117,f148,f160,f190,f195,f264,f285,f320,f676,f1004,f1016,f1210,f1305,f2361,f2711,f2745])).

fof(f2745,plain,
    ( spl3_64
    | ~ spl3_90 ),
    inference(avatar_contradiction_clause,[],[f2712])).

fof(f2712,plain,
    ( $false
    | spl3_64
    | ~ spl3_90 ),
    inference(unit_resulting_resolution,[],[f1304,f2710])).

fof(f2710,plain,
    ( ! [X0,X1] : k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)) = k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(sK2,X0)))
    | ~ spl3_90 ),
    inference(avatar_component_clause,[],[f2709])).

fof(f2709,plain,
    ( spl3_90
  <=> ! [X1,X0] : k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)) = k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(sK2,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_90])])).

fof(f1304,plain,
    ( k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | spl3_64 ),
    inference(avatar_component_clause,[],[f1302])).

fof(f1302,plain,
    ( spl3_64
  <=> k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f2711,plain,
    ( spl3_90
    | ~ spl3_84 ),
    inference(avatar_split_clause,[],[f2670,f2359,f2709])).

fof(f2359,plain,
    ( spl3_84
  <=> ! [X1,X0] : k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X1),X0)) = k1_setfam_1(k1_enumset1(k9_relat_1(sK2,X1),k9_relat_1(sK2,X1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).

fof(f2670,plain,
    ( ! [X0,X1] : k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)) = k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(sK2,X0)))
    | ~ spl3_84 ),
    inference(superposition,[],[f2360,f45])).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f32,f33,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f2360,plain,
    ( ! [X0,X1] : k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X1),X0)) = k1_setfam_1(k1_enumset1(k9_relat_1(sK2,X1),k9_relat_1(sK2,X1),X0))
    | ~ spl3_84 ),
    inference(avatar_component_clause,[],[f2359])).

fof(f2361,plain,
    ( spl3_84
    | ~ spl3_13
    | ~ spl3_26
    | ~ spl3_56
    | ~ spl3_59 ),
    inference(avatar_split_clause,[],[f2327,f1014,f1002,f318,f146,f2359])).

fof(f146,plain,
    ( spl3_13
  <=> ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f318,plain,
    ( spl3_26
  <=> ! [X18,X19] : k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X18,X18,X19))) = k9_relat_1(k7_relat_1(sK2,X18),X19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f1002,plain,
    ( spl3_56
  <=> ! [X1,X0,X2] : k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),X2) = k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(k7_relat_1(sK2,X0),X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f1014,plain,
    ( spl3_59
  <=> ! [X1,X0] : k9_relat_1(k7_relat_1(sK2,X0),k10_relat_1(k7_relat_1(sK2,X0),X1)) = k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(sK2,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f2327,plain,
    ( ! [X0,X1] : k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X1),X0)) = k1_setfam_1(k1_enumset1(k9_relat_1(sK2,X1),k9_relat_1(sK2,X1),X0))
    | ~ spl3_13
    | ~ spl3_26
    | ~ spl3_56
    | ~ spl3_59 ),
    inference(forward_demodulation,[],[f2326,f147])).

fof(f147,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),X0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f146])).

fof(f2326,plain,
    ( ! [X0,X1] : k1_setfam_1(k1_enumset1(k9_relat_1(sK2,X1),k9_relat_1(sK2,X1),X0)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X1),X0))
    | ~ spl3_26
    | ~ spl3_56
    | ~ spl3_59 ),
    inference(forward_demodulation,[],[f2295,f1029])).

fof(f1029,plain,
    ( ! [X4,X5,X3] : k9_relat_1(k7_relat_1(sK2,X3),k10_relat_1(k7_relat_1(sK2,X4),X5)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X4),X3),X5))
    | ~ spl3_26
    | ~ spl3_56 ),
    inference(superposition,[],[f319,f1003])).

fof(f1003,plain,
    ( ! [X2,X0,X1] : k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),X2) = k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(k7_relat_1(sK2,X0),X2)))
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f1002])).

fof(f319,plain,
    ( ! [X19,X18] : k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X18,X18,X19))) = k9_relat_1(k7_relat_1(sK2,X18),X19)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f318])).

fof(f2295,plain,
    ( ! [X0,X1] : k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X1),X0)) = k1_setfam_1(k1_enumset1(k9_relat_1(sK2,X1),k9_relat_1(sK2,X1),X0))
    | ~ spl3_59 ),
    inference(superposition,[],[f1015,f45])).

fof(f1015,plain,
    ( ! [X0,X1] : k9_relat_1(k7_relat_1(sK2,X0),k10_relat_1(k7_relat_1(sK2,X0),X1)) = k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(sK2,X0)))
    | ~ spl3_59 ),
    inference(avatar_component_clause,[],[f1014])).

fof(f1305,plain,
    ( ~ spl3_64
    | ~ spl3_26
    | ~ spl3_42
    | spl3_63 ),
    inference(avatar_split_clause,[],[f1213,f1207,f674,f318,f1302])).

fof(f674,plain,
    ( spl3_42
  <=> ! [X1,X0] : k9_relat_1(k7_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f1207,plain,
    ( spl3_63
  <=> k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) = k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).

fof(f1213,plain,
    ( k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | ~ spl3_26
    | ~ spl3_42
    | spl3_63 ),
    inference(forward_demodulation,[],[f1212,f675])).

fof(f675,plain,
    ( ! [X0,X1] : k9_relat_1(k7_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1))
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f674])).

fof(f1212,plain,
    ( k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_26
    | spl3_63 ),
    inference(forward_demodulation,[],[f1211,f319])).

fof(f1211,plain,
    ( k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))
    | spl3_63 ),
    inference(forward_demodulation,[],[f1209,f45])).

fof(f1209,plain,
    ( k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))
    | spl3_63 ),
    inference(avatar_component_clause,[],[f1207])).

fof(f1210,plain,(
    ~ spl3_63 ),
    inference(avatar_split_clause,[],[f44,f1207])).

fof(f44,plain,(
    k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)) ),
    inference(definition_unfolding,[],[f30,f43,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f33])).

fof(f34,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f30,plain,(
    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_funct_1)).

fof(f1016,plain,
    ( spl3_59
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f433,f193,f72,f61,f1014])).

fof(f61,plain,
    ( spl3_3
  <=> ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f72,plain,
    ( spl3_5
  <=> ! [X0] : v1_funct_1(k7_relat_1(sK2,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f193,plain,
    ( spl3_19
  <=> ! [X0] : k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k9_relat_1(sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f433,plain,
    ( ! [X0,X1] : k9_relat_1(k7_relat_1(sK2,X0),k10_relat_1(k7_relat_1(sK2,X0),X1)) = k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(sK2,X0)))
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f412,f194])).

fof(f194,plain,
    ( ! [X0] : k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k9_relat_1(sK2,X0)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f193])).

fof(f412,plain,
    ( ! [X0,X1] : k9_relat_1(k7_relat_1(sK2,X0),k10_relat_1(k7_relat_1(sK2,X0),X1)) = k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0)))))
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f62,f73,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1))))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f38,f43])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

fof(f73,plain,
    ( ! [X0] : v1_funct_1(k7_relat_1(sK2,X0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f62,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK2,X0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f1004,plain,
    ( spl3_56
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f247,f61,f1002])).

fof(f247,plain,
    ( ! [X2,X0,X1] : k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),X2) = k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(k7_relat_1(sK2,X0),X2)))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f62,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f41,f43])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f676,plain,
    ( spl3_42
    | ~ spl3_23
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f410,f318,f262,f674])).

fof(f262,plain,
    ( spl3_23
  <=> ! [X1,X0] : k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f410,plain,
    ( ! [X0,X1] : k9_relat_1(k7_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1))
    | ~ spl3_23
    | ~ spl3_26 ),
    inference(superposition,[],[f319,f263])).

fof(f263,plain,
    ( ! [X0,X1] : k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1)))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f262])).

fof(f320,plain,
    ( spl3_26
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f309,f283,f158,f115,f318])).

fof(f115,plain,
    ( spl3_10
  <=> ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f158,plain,
    ( spl3_14
  <=> ! [X1,X0] : k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)) = k9_relat_1(k7_relat_1(sK2,X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f283,plain,
    ( spl3_24
  <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f309,plain,
    ( ! [X19,X18] : k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X18,X18,X19))) = k9_relat_1(k7_relat_1(sK2,X18),X19)
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f295,f159])).

fof(f159,plain,
    ( ! [X0,X1] : k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)) = k9_relat_1(k7_relat_1(sK2,X0),X1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f158])).

fof(f295,plain,
    ( ! [X19,X18] : k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X18,X18,X19))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X18),X19))
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(superposition,[],[f116,f284])).

fof(f284,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1)))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f283])).

fof(f116,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f285,plain,
    ( spl3_24
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f267,f50,f283])).

fof(f50,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f267,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1)))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f52,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f52,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f264,plain,
    ( spl3_23
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f246,f50,f262])).

fof(f246,plain,
    ( ! [X0,X1] : k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1)))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f52,f47])).

fof(f195,plain,
    ( spl3_19
    | ~ spl3_10
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f191,f188,f115,f193])).

fof(f188,plain,
    ( spl3_18
  <=> ! [X0] : k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k2_relat_1(k7_relat_1(sK2,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f191,plain,
    ( ! [X0] : k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k9_relat_1(sK2,X0)
    | ~ spl3_10
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f189,f116])).

fof(f189,plain,
    ( ! [X0] : k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k2_relat_1(k7_relat_1(sK2,X0))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f188])).

fof(f190,plain,
    ( spl3_18
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f92,f61,f188])).

fof(f92,plain,
    ( ! [X0] : k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k2_relat_1(k7_relat_1(sK2,X0))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f62,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f160,plain,
    ( spl3_14
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f106,f61,f158])).

fof(f106,plain,
    ( ! [X0,X1] : k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)) = k9_relat_1(k7_relat_1(sK2,X0),X1)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f62,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f148,plain,
    ( spl3_13
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f134,f50,f146])).

fof(f134,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),X0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f52,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_relat_1)).

fof(f117,plain,
    ( spl3_10
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f105,f50,f115])).

fof(f105,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f52,f36])).

fof(f74,plain,
    ( spl3_5
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f70,f55,f50,f72])).

fof(f55,plain,
    ( spl3_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f70,plain,
    ( ! [X0] : v1_funct_1(k7_relat_1(sK2,X0))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f52,f57,f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f57,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f63,plain,
    ( spl3_3
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f59,f50,f61])).

fof(f59,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK2,X0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f52,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f58,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f29,f55])).

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f28,f50])).

fof(f28,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.31  % Computer   : n006.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 20:56:52 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.18/0.42  % (30182)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.18/0.42  % (30180)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.18/0.42  % (30172)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.18/0.44  % (30165)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.18/0.45  % (30169)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.18/0.46  % (30171)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.18/0.46  % (30166)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.18/0.46  % (30168)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.18/0.47  % (30181)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.18/0.47  % (30177)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.18/0.48  % (30176)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.18/0.48  % (30175)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.18/0.48  % (30164)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.18/0.48  % (30170)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.18/0.48  % (30174)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.18/0.49  % (30179)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.18/0.49  % (30183)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.18/0.51  % (30178)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 2.17/0.62  % (30183)Refutation found. Thanks to Tanya!
% 2.17/0.62  % SZS status Theorem for theBenchmark
% 2.17/0.62  % SZS output start Proof for theBenchmark
% 2.17/0.62  fof(f2755,plain,(
% 2.17/0.62    $false),
% 2.17/0.62    inference(avatar_sat_refutation,[],[f53,f58,f63,f74,f117,f148,f160,f190,f195,f264,f285,f320,f676,f1004,f1016,f1210,f1305,f2361,f2711,f2745])).
% 2.17/0.62  fof(f2745,plain,(
% 2.17/0.62    spl3_64 | ~spl3_90),
% 2.17/0.62    inference(avatar_contradiction_clause,[],[f2712])).
% 2.17/0.62  fof(f2712,plain,(
% 2.17/0.62    $false | (spl3_64 | ~spl3_90)),
% 2.17/0.62    inference(unit_resulting_resolution,[],[f1304,f2710])).
% 2.17/0.62  fof(f2710,plain,(
% 2.17/0.62    ( ! [X0,X1] : (k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)) = k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(sK2,X0)))) ) | ~spl3_90),
% 2.17/0.62    inference(avatar_component_clause,[],[f2709])).
% 2.17/0.62  fof(f2709,plain,(
% 2.17/0.62    spl3_90 <=> ! [X1,X0] : k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)) = k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(sK2,X0)))),
% 2.17/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_90])])).
% 2.17/0.62  fof(f1304,plain,(
% 2.17/0.62    k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) | spl3_64),
% 2.17/0.62    inference(avatar_component_clause,[],[f1302])).
% 2.17/0.62  fof(f1302,plain,(
% 2.17/0.62    spl3_64 <=> k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1))),
% 2.17/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 2.17/0.62  fof(f2711,plain,(
% 2.17/0.62    spl3_90 | ~spl3_84),
% 2.17/0.62    inference(avatar_split_clause,[],[f2670,f2359,f2709])).
% 2.17/0.62  fof(f2359,plain,(
% 2.17/0.62    spl3_84 <=> ! [X1,X0] : k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X1),X0)) = k1_setfam_1(k1_enumset1(k9_relat_1(sK2,X1),k9_relat_1(sK2,X1),X0))),
% 2.17/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).
% 2.17/0.62  fof(f2670,plain,(
% 2.17/0.62    ( ! [X0,X1] : (k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)) = k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(sK2,X0)))) ) | ~spl3_84),
% 2.17/0.62    inference(superposition,[],[f2360,f45])).
% 2.17/0.62  fof(f45,plain,(
% 2.17/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 2.17/0.62    inference(definition_unfolding,[],[f32,f33,f33])).
% 2.17/0.62  fof(f33,plain,(
% 2.17/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.17/0.62    inference(cnf_transformation,[],[f2])).
% 2.17/0.62  fof(f2,axiom,(
% 2.17/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.17/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.17/0.62  fof(f32,plain,(
% 2.17/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.17/0.62    inference(cnf_transformation,[],[f1])).
% 2.17/0.62  fof(f1,axiom,(
% 2.17/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.17/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.17/0.62  fof(f2360,plain,(
% 2.17/0.62    ( ! [X0,X1] : (k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X1),X0)) = k1_setfam_1(k1_enumset1(k9_relat_1(sK2,X1),k9_relat_1(sK2,X1),X0))) ) | ~spl3_84),
% 2.17/0.62    inference(avatar_component_clause,[],[f2359])).
% 2.17/0.62  fof(f2361,plain,(
% 2.17/0.62    spl3_84 | ~spl3_13 | ~spl3_26 | ~spl3_56 | ~spl3_59),
% 2.17/0.62    inference(avatar_split_clause,[],[f2327,f1014,f1002,f318,f146,f2359])).
% 2.17/0.62  fof(f146,plain,(
% 2.17/0.62    spl3_13 <=> ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),X0)),
% 2.17/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 2.17/0.62  fof(f318,plain,(
% 2.17/0.62    spl3_26 <=> ! [X18,X19] : k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X18,X18,X19))) = k9_relat_1(k7_relat_1(sK2,X18),X19)),
% 2.17/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 2.17/0.62  fof(f1002,plain,(
% 2.17/0.62    spl3_56 <=> ! [X1,X0,X2] : k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),X2) = k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(k7_relat_1(sK2,X0),X2)))),
% 2.17/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 2.17/0.62  fof(f1014,plain,(
% 2.17/0.62    spl3_59 <=> ! [X1,X0] : k9_relat_1(k7_relat_1(sK2,X0),k10_relat_1(k7_relat_1(sK2,X0),X1)) = k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(sK2,X0)))),
% 2.17/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 2.17/0.62  fof(f2327,plain,(
% 2.17/0.62    ( ! [X0,X1] : (k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X1),X0)) = k1_setfam_1(k1_enumset1(k9_relat_1(sK2,X1),k9_relat_1(sK2,X1),X0))) ) | (~spl3_13 | ~spl3_26 | ~spl3_56 | ~spl3_59)),
% 2.17/0.62    inference(forward_demodulation,[],[f2326,f147])).
% 2.17/0.62  fof(f147,plain,(
% 2.17/0.62    ( ! [X0] : (k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),X0)) ) | ~spl3_13),
% 2.17/0.62    inference(avatar_component_clause,[],[f146])).
% 2.17/0.62  fof(f2326,plain,(
% 2.17/0.62    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(k9_relat_1(sK2,X1),k9_relat_1(sK2,X1),X0)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X1),X0))) ) | (~spl3_26 | ~spl3_56 | ~spl3_59)),
% 2.17/0.62    inference(forward_demodulation,[],[f2295,f1029])).
% 2.17/0.62  fof(f1029,plain,(
% 2.17/0.62    ( ! [X4,X5,X3] : (k9_relat_1(k7_relat_1(sK2,X3),k10_relat_1(k7_relat_1(sK2,X4),X5)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X4),X3),X5))) ) | (~spl3_26 | ~spl3_56)),
% 2.17/0.62    inference(superposition,[],[f319,f1003])).
% 2.17/0.62  fof(f1003,plain,(
% 2.17/0.62    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),X2) = k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(k7_relat_1(sK2,X0),X2)))) ) | ~spl3_56),
% 2.17/0.62    inference(avatar_component_clause,[],[f1002])).
% 2.17/0.62  fof(f319,plain,(
% 2.17/0.62    ( ! [X19,X18] : (k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X18,X18,X19))) = k9_relat_1(k7_relat_1(sK2,X18),X19)) ) | ~spl3_26),
% 2.17/0.62    inference(avatar_component_clause,[],[f318])).
% 2.17/0.62  fof(f2295,plain,(
% 2.17/0.62    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X1),X0)) = k1_setfam_1(k1_enumset1(k9_relat_1(sK2,X1),k9_relat_1(sK2,X1),X0))) ) | ~spl3_59),
% 2.17/0.62    inference(superposition,[],[f1015,f45])).
% 2.17/0.62  fof(f1015,plain,(
% 2.17/0.62    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),k10_relat_1(k7_relat_1(sK2,X0),X1)) = k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(sK2,X0)))) ) | ~spl3_59),
% 2.17/0.62    inference(avatar_component_clause,[],[f1014])).
% 2.17/0.62  fof(f1305,plain,(
% 2.17/0.62    ~spl3_64 | ~spl3_26 | ~spl3_42 | spl3_63),
% 2.17/0.62    inference(avatar_split_clause,[],[f1213,f1207,f674,f318,f1302])).
% 2.17/0.62  fof(f674,plain,(
% 2.17/0.62    spl3_42 <=> ! [X1,X0] : k9_relat_1(k7_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1))),
% 2.17/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 2.17/0.62  fof(f1207,plain,(
% 2.17/0.62    spl3_63 <=> k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) = k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))),
% 2.17/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).
% 2.17/0.62  fof(f1213,plain,(
% 2.17/0.62    k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) | (~spl3_26 | ~spl3_42 | spl3_63)),
% 2.17/0.62    inference(forward_demodulation,[],[f1212,f675])).
% 2.17/0.62  fof(f675,plain,(
% 2.17/0.62    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1))) ) | ~spl3_42),
% 2.17/0.62    inference(avatar_component_clause,[],[f674])).
% 2.17/0.62  fof(f1212,plain,(
% 2.17/0.62    k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | (~spl3_26 | spl3_63)),
% 2.17/0.62    inference(forward_demodulation,[],[f1211,f319])).
% 2.17/0.62  fof(f1211,plain,(
% 2.17/0.62    k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) | spl3_63),
% 2.17/0.62    inference(forward_demodulation,[],[f1209,f45])).
% 2.17/0.62  fof(f1209,plain,(
% 2.17/0.62    k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)) | spl3_63),
% 2.17/0.62    inference(avatar_component_clause,[],[f1207])).
% 2.17/0.62  fof(f1210,plain,(
% 2.17/0.62    ~spl3_63),
% 2.17/0.62    inference(avatar_split_clause,[],[f44,f1207])).
% 2.17/0.62  fof(f44,plain,(
% 2.17/0.62    k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))),
% 2.17/0.62    inference(definition_unfolding,[],[f30,f43,f43])).
% 2.17/0.62  fof(f43,plain,(
% 2.17/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 2.17/0.62    inference(definition_unfolding,[],[f34,f33])).
% 2.17/0.62  fof(f34,plain,(
% 2.17/0.62    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.17/0.62    inference(cnf_transformation,[],[f3])).
% 2.17/0.62  fof(f3,axiom,(
% 2.17/0.62    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.17/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.17/0.62  fof(f30,plain,(
% 2.17/0.62    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1)),
% 2.17/0.62    inference(cnf_transformation,[],[f27])).
% 2.17/0.62  fof(f27,plain,(
% 2.17/0.62    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 2.17/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f26])).
% 2.17/0.62  fof(f26,plain,(
% 2.17/0.62    ? [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1) & v1_funct_1(X2) & v1_relat_1(X2)) => (k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 2.17/0.62    introduced(choice_axiom,[])).
% 2.17/0.62  fof(f15,plain,(
% 2.17/0.62    ? [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 2.17/0.62    inference(flattening,[],[f14])).
% 2.17/0.62  fof(f14,plain,(
% 2.17/0.62    ? [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 2.17/0.62    inference(ennf_transformation,[],[f13])).
% 2.17/0.62  fof(f13,negated_conjecture,(
% 2.17/0.62    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1))),
% 2.17/0.62    inference(negated_conjecture,[],[f12])).
% 2.17/0.62  fof(f12,conjecture,(
% 2.17/0.62    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1))),
% 2.17/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_funct_1)).
% 2.17/0.62  fof(f1016,plain,(
% 2.17/0.62    spl3_59 | ~spl3_3 | ~spl3_5 | ~spl3_19),
% 2.17/0.62    inference(avatar_split_clause,[],[f433,f193,f72,f61,f1014])).
% 2.17/0.62  fof(f61,plain,(
% 2.17/0.62    spl3_3 <=> ! [X0] : v1_relat_1(k7_relat_1(sK2,X0))),
% 2.17/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.17/0.62  fof(f72,plain,(
% 2.17/0.62    spl3_5 <=> ! [X0] : v1_funct_1(k7_relat_1(sK2,X0))),
% 2.17/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.17/0.62  fof(f193,plain,(
% 2.17/0.62    spl3_19 <=> ! [X0] : k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k9_relat_1(sK2,X0)),
% 2.17/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 2.17/0.62  fof(f433,plain,(
% 2.17/0.62    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),k10_relat_1(k7_relat_1(sK2,X0),X1)) = k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(sK2,X0)))) ) | (~spl3_3 | ~spl3_5 | ~spl3_19)),
% 2.17/0.62    inference(forward_demodulation,[],[f412,f194])).
% 2.17/0.62  fof(f194,plain,(
% 2.17/0.62    ( ! [X0] : (k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k9_relat_1(sK2,X0)) ) | ~spl3_19),
% 2.17/0.62    inference(avatar_component_clause,[],[f193])).
% 2.17/0.62  fof(f412,plain,(
% 2.17/0.62    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),k10_relat_1(k7_relat_1(sK2,X0),X1)) = k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0)))))) ) | (~spl3_3 | ~spl3_5)),
% 2.17/0.62    inference(unit_resulting_resolution,[],[f62,f73,f46])).
% 2.17/0.62  fof(f46,plain,(
% 2.17/0.62    ( ! [X0,X1] : (~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) | ~v1_relat_1(X1)) )),
% 2.17/0.62    inference(definition_unfolding,[],[f38,f43])).
% 2.17/0.62  fof(f38,plain,(
% 2.17/0.62    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.17/0.62    inference(cnf_transformation,[],[f21])).
% 2.17/0.62  fof(f21,plain,(
% 2.17/0.62    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.17/0.62    inference(flattening,[],[f20])).
% 2.17/0.62  fof(f20,plain,(
% 2.17/0.62    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.17/0.62    inference(ennf_transformation,[],[f11])).
% 2.17/0.62  fof(f11,axiom,(
% 2.17/0.62    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 2.17/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).
% 2.17/0.62  fof(f73,plain,(
% 2.17/0.62    ( ! [X0] : (v1_funct_1(k7_relat_1(sK2,X0))) ) | ~spl3_5),
% 2.17/0.62    inference(avatar_component_clause,[],[f72])).
% 2.17/0.62  fof(f62,plain,(
% 2.17/0.62    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) ) | ~spl3_3),
% 2.17/0.62    inference(avatar_component_clause,[],[f61])).
% 2.17/0.62  fof(f1004,plain,(
% 2.17/0.62    spl3_56 | ~spl3_3),
% 2.17/0.62    inference(avatar_split_clause,[],[f247,f61,f1002])).
% 2.17/0.62  fof(f247,plain,(
% 2.17/0.62    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),X2) = k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(k7_relat_1(sK2,X0),X2)))) ) | ~spl3_3),
% 2.17/0.62    inference(unit_resulting_resolution,[],[f62,f47])).
% 2.17/0.62  fof(f47,plain,(
% 2.17/0.62    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1)))) )),
% 2.17/0.62    inference(definition_unfolding,[],[f41,f43])).
% 2.17/0.62  fof(f41,plain,(
% 2.17/0.62    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.17/0.62    inference(cnf_transformation,[],[f24])).
% 2.17/0.62  fof(f24,plain,(
% 2.17/0.62    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.17/0.62    inference(ennf_transformation,[],[f10])).
% 2.17/0.62  fof(f10,axiom,(
% 2.17/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 2.17/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 2.17/0.62  fof(f676,plain,(
% 2.17/0.62    spl3_42 | ~spl3_23 | ~spl3_26),
% 2.17/0.62    inference(avatar_split_clause,[],[f410,f318,f262,f674])).
% 2.17/0.62  fof(f262,plain,(
% 2.17/0.62    spl3_23 <=> ! [X1,X0] : k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1)))),
% 2.17/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 2.17/0.62  fof(f410,plain,(
% 2.17/0.62    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1))) ) | (~spl3_23 | ~spl3_26)),
% 2.17/0.62    inference(superposition,[],[f319,f263])).
% 2.17/0.62  fof(f263,plain,(
% 2.17/0.62    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1)))) ) | ~spl3_23),
% 2.17/0.62    inference(avatar_component_clause,[],[f262])).
% 2.17/0.62  fof(f320,plain,(
% 2.17/0.62    spl3_26 | ~spl3_10 | ~spl3_14 | ~spl3_24),
% 2.17/0.62    inference(avatar_split_clause,[],[f309,f283,f158,f115,f318])).
% 2.17/0.62  fof(f115,plain,(
% 2.17/0.62    spl3_10 <=> ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)),
% 2.17/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 2.17/0.62  fof(f158,plain,(
% 2.17/0.62    spl3_14 <=> ! [X1,X0] : k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)) = k9_relat_1(k7_relat_1(sK2,X0),X1)),
% 2.17/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 2.17/0.62  fof(f283,plain,(
% 2.17/0.62    spl3_24 <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1)))),
% 2.17/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 2.17/0.62  fof(f309,plain,(
% 2.17/0.62    ( ! [X19,X18] : (k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X18,X18,X19))) = k9_relat_1(k7_relat_1(sK2,X18),X19)) ) | (~spl3_10 | ~spl3_14 | ~spl3_24)),
% 2.17/0.62    inference(forward_demodulation,[],[f295,f159])).
% 2.17/0.62  fof(f159,plain,(
% 2.17/0.62    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)) = k9_relat_1(k7_relat_1(sK2,X0),X1)) ) | ~spl3_14),
% 2.17/0.62    inference(avatar_component_clause,[],[f158])).
% 2.17/0.62  fof(f295,plain,(
% 2.17/0.62    ( ! [X19,X18] : (k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X18,X18,X19))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X18),X19))) ) | (~spl3_10 | ~spl3_24)),
% 2.17/0.62    inference(superposition,[],[f116,f284])).
% 2.17/0.62  fof(f284,plain,(
% 2.17/0.62    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1)))) ) | ~spl3_24),
% 2.17/0.62    inference(avatar_component_clause,[],[f283])).
% 2.17/0.62  fof(f116,plain,(
% 2.17/0.62    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) ) | ~spl3_10),
% 2.17/0.62    inference(avatar_component_clause,[],[f115])).
% 2.17/0.62  fof(f285,plain,(
% 2.17/0.62    spl3_24 | ~spl3_1),
% 2.17/0.62    inference(avatar_split_clause,[],[f267,f50,f283])).
% 2.17/0.62  fof(f50,plain,(
% 2.17/0.62    spl3_1 <=> v1_relat_1(sK2)),
% 2.17/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.17/0.62  fof(f267,plain,(
% 2.17/0.62    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1)))) ) | ~spl3_1),
% 2.17/0.62    inference(unit_resulting_resolution,[],[f52,f48])).
% 2.17/0.62  fof(f48,plain,(
% 2.17/0.62    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 2.17/0.62    inference(definition_unfolding,[],[f42,f43])).
% 2.17/0.62  fof(f42,plain,(
% 2.17/0.62    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 2.17/0.62    inference(cnf_transformation,[],[f25])).
% 2.17/0.62  fof(f25,plain,(
% 2.17/0.62    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 2.17/0.62    inference(ennf_transformation,[],[f5])).
% 2.17/0.62  fof(f5,axiom,(
% 2.17/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 2.17/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 2.17/0.62  fof(f52,plain,(
% 2.17/0.62    v1_relat_1(sK2) | ~spl3_1),
% 2.17/0.62    inference(avatar_component_clause,[],[f50])).
% 2.17/0.62  fof(f264,plain,(
% 2.17/0.62    spl3_23 | ~spl3_1),
% 2.17/0.62    inference(avatar_split_clause,[],[f246,f50,f262])).
% 2.17/0.62  fof(f246,plain,(
% 2.17/0.62    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1)))) ) | ~spl3_1),
% 2.17/0.62    inference(unit_resulting_resolution,[],[f52,f47])).
% 2.17/0.62  fof(f195,plain,(
% 2.17/0.62    spl3_19 | ~spl3_10 | ~spl3_18),
% 2.17/0.62    inference(avatar_split_clause,[],[f191,f188,f115,f193])).
% 2.17/0.62  fof(f188,plain,(
% 2.17/0.62    spl3_18 <=> ! [X0] : k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k2_relat_1(k7_relat_1(sK2,X0))),
% 2.17/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 2.17/0.62  fof(f191,plain,(
% 2.17/0.62    ( ! [X0] : (k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k9_relat_1(sK2,X0)) ) | (~spl3_10 | ~spl3_18)),
% 2.17/0.62    inference(forward_demodulation,[],[f189,f116])).
% 2.17/0.62  fof(f189,plain,(
% 2.17/0.62    ( ! [X0] : (k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k2_relat_1(k7_relat_1(sK2,X0))) ) | ~spl3_18),
% 2.17/0.62    inference(avatar_component_clause,[],[f188])).
% 2.17/0.62  fof(f190,plain,(
% 2.17/0.62    spl3_18 | ~spl3_3),
% 2.17/0.62    inference(avatar_split_clause,[],[f92,f61,f188])).
% 2.17/0.62  fof(f92,plain,(
% 2.17/0.62    ( ! [X0] : (k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k2_relat_1(k7_relat_1(sK2,X0))) ) | ~spl3_3),
% 2.17/0.62    inference(unit_resulting_resolution,[],[f62,f31])).
% 2.17/0.62  fof(f31,plain,(
% 2.17/0.62    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 2.17/0.62    inference(cnf_transformation,[],[f16])).
% 2.17/0.62  fof(f16,plain,(
% 2.17/0.62    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.17/0.62    inference(ennf_transformation,[],[f7])).
% 2.17/0.62  fof(f7,axiom,(
% 2.17/0.62    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.17/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 2.17/0.62  fof(f160,plain,(
% 2.17/0.62    spl3_14 | ~spl3_3),
% 2.17/0.62    inference(avatar_split_clause,[],[f106,f61,f158])).
% 2.17/0.62  fof(f106,plain,(
% 2.17/0.62    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)) = k9_relat_1(k7_relat_1(sK2,X0),X1)) ) | ~spl3_3),
% 2.17/0.62    inference(unit_resulting_resolution,[],[f62,f36])).
% 2.17/0.62  fof(f36,plain,(
% 2.17/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 2.17/0.62    inference(cnf_transformation,[],[f18])).
% 2.17/0.62  fof(f18,plain,(
% 2.17/0.62    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.17/0.62    inference(ennf_transformation,[],[f8])).
% 2.17/0.62  fof(f8,axiom,(
% 2.17/0.62    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.17/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 2.17/0.62  fof(f148,plain,(
% 2.17/0.62    spl3_13 | ~spl3_1),
% 2.17/0.62    inference(avatar_split_clause,[],[f134,f50,f146])).
% 2.17/0.62  fof(f134,plain,(
% 2.17/0.62    ( ! [X0] : (k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),X0)) ) | ~spl3_1),
% 2.17/0.62    inference(unit_resulting_resolution,[],[f52,f37])).
% 2.17/0.62  fof(f37,plain,(
% 2.17/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0)) )),
% 2.17/0.62    inference(cnf_transformation,[],[f19])).
% 2.17/0.62  fof(f19,plain,(
% 2.17/0.62    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) | ~v1_relat_1(X1))),
% 2.17/0.62    inference(ennf_transformation,[],[f6])).
% 2.17/0.62  fof(f6,axiom,(
% 2.17/0.62    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0))),
% 2.17/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_relat_1)).
% 2.17/0.62  fof(f117,plain,(
% 2.17/0.62    spl3_10 | ~spl3_1),
% 2.17/0.62    inference(avatar_split_clause,[],[f105,f50,f115])).
% 2.17/0.62  fof(f105,plain,(
% 2.17/0.62    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) ) | ~spl3_1),
% 2.17/0.62    inference(unit_resulting_resolution,[],[f52,f36])).
% 2.17/0.62  fof(f74,plain,(
% 2.17/0.62    spl3_5 | ~spl3_1 | ~spl3_2),
% 2.17/0.62    inference(avatar_split_clause,[],[f70,f55,f50,f72])).
% 2.17/0.62  fof(f55,plain,(
% 2.17/0.62    spl3_2 <=> v1_funct_1(sK2)),
% 2.17/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.17/0.62  fof(f70,plain,(
% 2.17/0.62    ( ! [X0] : (v1_funct_1(k7_relat_1(sK2,X0))) ) | (~spl3_1 | ~spl3_2)),
% 2.17/0.62    inference(unit_resulting_resolution,[],[f52,f57,f40])).
% 2.17/0.62  fof(f40,plain,(
% 2.17/0.62    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.17/0.62    inference(cnf_transformation,[],[f23])).
% 2.17/0.62  fof(f23,plain,(
% 2.17/0.62    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.17/0.62    inference(flattening,[],[f22])).
% 2.17/0.62  fof(f22,plain,(
% 2.17/0.62    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.17/0.62    inference(ennf_transformation,[],[f9])).
% 2.17/0.62  fof(f9,axiom,(
% 2.17/0.62    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 2.17/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).
% 2.17/0.62  fof(f57,plain,(
% 2.17/0.62    v1_funct_1(sK2) | ~spl3_2),
% 2.17/0.62    inference(avatar_component_clause,[],[f55])).
% 2.17/0.62  fof(f63,plain,(
% 2.17/0.62    spl3_3 | ~spl3_1),
% 2.17/0.62    inference(avatar_split_clause,[],[f59,f50,f61])).
% 2.17/0.62  fof(f59,plain,(
% 2.17/0.62    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) ) | ~spl3_1),
% 2.17/0.62    inference(unit_resulting_resolution,[],[f52,f35])).
% 2.17/0.62  fof(f35,plain,(
% 2.17/0.62    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.17/0.62    inference(cnf_transformation,[],[f17])).
% 2.17/0.62  fof(f17,plain,(
% 2.17/0.62    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.17/0.62    inference(ennf_transformation,[],[f4])).
% 2.17/0.62  fof(f4,axiom,(
% 2.17/0.62    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.17/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.17/0.62  fof(f58,plain,(
% 2.17/0.62    spl3_2),
% 2.17/0.62    inference(avatar_split_clause,[],[f29,f55])).
% 2.17/0.62  fof(f29,plain,(
% 2.17/0.62    v1_funct_1(sK2)),
% 2.17/0.62    inference(cnf_transformation,[],[f27])).
% 2.17/0.62  fof(f53,plain,(
% 2.17/0.62    spl3_1),
% 2.17/0.62    inference(avatar_split_clause,[],[f28,f50])).
% 2.17/0.62  fof(f28,plain,(
% 2.17/0.62    v1_relat_1(sK2)),
% 2.17/0.62    inference(cnf_transformation,[],[f27])).
% 2.17/0.62  % SZS output end Proof for theBenchmark
% 2.17/0.62  % (30183)------------------------------
% 2.17/0.62  % (30183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.62  % (30183)Termination reason: Refutation
% 2.17/0.62  
% 2.17/0.62  % (30183)Memory used [KB]: 13048
% 2.17/0.62  % (30183)Time elapsed: 0.219 s
% 2.17/0.62  % (30183)------------------------------
% 2.17/0.62  % (30183)------------------------------
% 2.17/0.62  % (30157)Success in time 0.291 s
%------------------------------------------------------------------------------
