%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:53 EST 2020

% Result     : Theorem 2.79s
% Output     : Refutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 231 expanded)
%              Number of leaves         :   27 (  91 expanded)
%              Depth                    :    8
%              Number of atoms          :  213 ( 425 expanded)
%              Number of equality atoms :   45 ( 127 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4112,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f74,f475,f3014,f3019,f3093,f3185,f3367,f3420,f3561,f3653,f3700,f3731,f3785,f3916])).

fof(f3916,plain,
    ( ~ spl5_81
    | spl5_87
    | ~ spl5_96 ),
    inference(avatar_contradiction_clause,[],[f3915])).

fof(f3915,plain,
    ( $false
    | ~ spl5_81
    | spl5_87
    | ~ spl5_96 ),
    inference(global_subsumption,[],[f37,f3846])).

fof(f3846,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK2),sK1)
    | ~ spl5_81
    | ~ spl5_96 ),
    inference(unit_resulting_resolution,[],[f3784,f3419,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)
      | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X2)
      | r1_tarski(k5_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f54,f45,f45])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X1),X2)
      | ~ r1_tarski(k4_xboole_0(X1,X0),X2)
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X1),X2)
      | ~ r1_tarski(k4_xboole_0(X1,X0),X2)
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X1),X2)
      | ~ r1_tarski(k4_xboole_0(X1,X0),X2)
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k4_xboole_0(X1,X0),X2)
        & r1_tarski(k4_xboole_0(X0,X1),X2) )
     => r1_tarski(k5_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_xboole_1)).

fof(f3419,plain,
    ( ! [X0] : r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),sK1)
    | ~ spl5_81 ),
    inference(avatar_component_clause,[],[f3418])).

fof(f3418,plain,
    ( spl5_81
  <=> ! [X0] : r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).

fof(f3784,plain,
    ( ! [X0] : r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,X0)),sK1)
    | ~ spl5_96 ),
    inference(avatar_component_clause,[],[f3783])).

fof(f3783,plain,
    ( spl5_96
  <=> ! [X0] : r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,X0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).

fof(f37,plain,(
    ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK2,sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK2,sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X2,X1)
          & r1_tarski(X0,X1) )
       => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f3785,plain,
    ( spl5_96
    | ~ spl5_91 ),
    inference(avatar_split_clause,[],[f3734,f3729,f3783])).

fof(f3729,plain,
    ( spl5_91
  <=> ! [X2] :
        ( ~ r1_tarski(X2,sK2)
        | r1_tarski(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).

fof(f3734,plain,
    ( ! [X0] : r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,X0)),sK1)
    | ~ spl5_91 ),
    inference(unit_resulting_resolution,[],[f56,f3730])).

fof(f3730,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK2)
        | r1_tarski(X2,sK1) )
    | ~ spl5_91 ),
    inference(avatar_component_clause,[],[f3729])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f41,f45])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f3731,plain,
    ( spl5_91
    | ~ spl5_84 ),
    inference(avatar_split_clause,[],[f3672,f3650,f3729])).

fof(f3650,plain,
    ( spl5_84
  <=> sK2 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f3672,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK2)
        | r1_tarski(X2,sK1) )
    | ~ spl5_84 ),
    inference(superposition,[],[f53,f3652])).

fof(f3652,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl5_84 ),
    inference(avatar_component_clause,[],[f3650])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f3700,plain,
    ( ~ spl5_87
    | ~ spl5_22
    | ~ spl5_84 ),
    inference(avatar_split_clause,[],[f3667,f3650,f473,f3697])).

fof(f3697,plain,
    ( spl5_87
  <=> r1_tarski(k5_xboole_0(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f473,plain,
    ( spl5_22
  <=> ! [X0] : ~ r1_tarski(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f3667,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK2)
    | ~ spl5_22
    | ~ spl5_84 ),
    inference(superposition,[],[f474,f3652])).

fof(f474,plain,
    ( ! [X0] : ~ r1_tarski(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f473])).

fof(f3653,plain,
    ( spl5_84
    | ~ spl5_83 ),
    inference(avatar_split_clause,[],[f3616,f3558,f3650])).

fof(f3558,plain,
    ( spl5_83
  <=> k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).

fof(f3616,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl5_83 ),
    inference(forward_demodulation,[],[f3576,f39])).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f3576,plain,
    ( k5_xboole_0(sK2,k1_xboole_0) = k3_xboole_0(sK1,sK2)
    | ~ spl5_83 ),
    inference(superposition,[],[f1234,f3560])).

fof(f3560,plain,
    ( k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))
    | ~ spl5_83 ),
    inference(avatar_component_clause,[],[f3558])).

fof(f1234,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f1206,f75])).

fof(f75,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f42,f39])).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f1206,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f52,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f52,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f3561,plain,
    ( spl5_83
    | ~ spl5_61 ),
    inference(avatar_split_clause,[],[f3530,f3016,f3558])).

fof(f3016,plain,
    ( spl5_61
  <=> sK1 = k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f3530,plain,
    ( k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f3529,f1234])).

fof(f3529,plain,
    ( k1_xboole_0 = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f3495,f42])).

fof(f3495,plain,
    ( k1_xboole_0 = k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1))
    | ~ spl5_61 ),
    inference(superposition,[],[f1212,f3018])).

fof(f3018,plain,
    ( sK1 = k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl5_61 ),
    inference(avatar_component_clause,[],[f3016])).

fof(f1212,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f52,f38])).

fof(f3420,plain,
    ( spl5_81
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f3369,f3365,f3418])).

fof(f3365,plain,
    ( spl5_76
  <=> ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | r1_tarski(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f3369,plain,
    ( ! [X0] : r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),sK1)
    | ~ spl5_76 ),
    inference(unit_resulting_resolution,[],[f56,f3366])).

fof(f3366,plain,
    ( ! [X2] :
        ( r1_tarski(X2,sK1)
        | ~ r1_tarski(X2,sK0) )
    | ~ spl5_76 ),
    inference(avatar_component_clause,[],[f3365])).

fof(f3367,plain,
    ( spl5_76
    | ~ spl5_63 ),
    inference(avatar_split_clause,[],[f3204,f3182,f3365])).

fof(f3182,plain,
    ( spl5_63
  <=> sK0 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f3204,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | r1_tarski(X2,sK1) )
    | ~ spl5_63 ),
    inference(superposition,[],[f53,f3184])).

fof(f3184,plain,
    ( sK0 = k3_xboole_0(sK1,sK0)
    | ~ spl5_63 ),
    inference(avatar_component_clause,[],[f3182])).

fof(f3185,plain,
    ( spl5_63
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f3148,f3090,f3182])).

fof(f3090,plain,
    ( spl5_62
  <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f3148,plain,
    ( sK0 = k3_xboole_0(sK1,sK0)
    | ~ spl5_62 ),
    inference(forward_demodulation,[],[f3108,f39])).

fof(f3108,plain,
    ( k5_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK1,sK0)
    | ~ spl5_62 ),
    inference(superposition,[],[f1234,f3092])).

fof(f3092,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK1,sK0))
    | ~ spl5_62 ),
    inference(avatar_component_clause,[],[f3090])).

fof(f3093,plain,
    ( spl5_62
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f3066,f3011,f3090])).

fof(f3011,plain,
    ( spl5_60
  <=> sK1 = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f3066,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK1,sK0))
    | ~ spl5_60 ),
    inference(forward_demodulation,[],[f3065,f1234])).

fof(f3065,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))
    | ~ spl5_60 ),
    inference(forward_demodulation,[],[f3031,f42])).

fof(f3031,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)),sK1))
    | ~ spl5_60 ),
    inference(superposition,[],[f1212,f3013])).

fof(f3013,plain,
    ( sK1 = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f3011])).

fof(f3019,plain,
    ( spl5_61
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f2997,f66,f3016])).

fof(f66,plain,
    ( spl5_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f2997,plain,
    ( sK1 = k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f68,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ) ),
    inference(definition_unfolding,[],[f49,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f68,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f3014,plain,
    ( spl5_60
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f2996,f61,f3011])).

fof(f61,plain,
    ( spl5_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f2996,plain,
    ( sK1 = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f63,f58])).

fof(f63,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f475,plain,
    ( spl5_22
    | spl5_3 ),
    inference(avatar_split_clause,[],[f405,f71,f473])).

fof(f71,plain,
    ( spl5_3
  <=> r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f405,plain,
    ( ! [X0] : ~ r1_tarski(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0))
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f73,f53])).

fof(f73,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f74,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f37,f71])).

fof(f69,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f36,f66])).

fof(f36,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f35,f61])).

fof(f35,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n021.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 14:03:19 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.45  % (24253)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (24260)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (24254)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (24250)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (24255)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (24258)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (24262)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (24252)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (24259)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (24263)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (24256)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (24267)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (24251)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (24264)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.51  % (24266)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.52  % (24265)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.53  % (24257)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.55  % (24261)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 2.79/0.71  % (24267)Refutation found. Thanks to Tanya!
% 2.79/0.71  % SZS status Theorem for theBenchmark
% 2.79/0.71  % SZS output start Proof for theBenchmark
% 2.79/0.71  fof(f4112,plain,(
% 2.79/0.71    $false),
% 2.79/0.71    inference(avatar_sat_refutation,[],[f64,f69,f74,f475,f3014,f3019,f3093,f3185,f3367,f3420,f3561,f3653,f3700,f3731,f3785,f3916])).
% 2.79/0.71  fof(f3916,plain,(
% 2.79/0.71    ~spl5_81 | spl5_87 | ~spl5_96),
% 2.79/0.71    inference(avatar_contradiction_clause,[],[f3915])).
% 2.79/0.71  fof(f3915,plain,(
% 2.79/0.71    $false | (~spl5_81 | spl5_87 | ~spl5_96)),
% 2.79/0.71    inference(global_subsumption,[],[f37,f3846])).
% 2.79/0.71  fof(f3846,plain,(
% 2.79/0.71    r1_tarski(k5_xboole_0(sK0,sK2),sK1) | (~spl5_81 | ~spl5_96)),
% 2.79/0.71    inference(unit_resulting_resolution,[],[f3784,f3419,f59])).
% 2.79/0.71  fof(f59,plain,(
% 2.79/0.71    ( ! [X2,X0,X1] : (~r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) | ~r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X2) | r1_tarski(k5_xboole_0(X0,X1),X2)) )),
% 2.79/0.71    inference(definition_unfolding,[],[f54,f45,f45])).
% 2.79/0.71  fof(f45,plain,(
% 2.79/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.79/0.71    inference(cnf_transformation,[],[f5])).
% 2.79/0.71  fof(f5,axiom,(
% 2.79/0.71    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.79/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.79/0.71  fof(f54,plain,(
% 2.79/0.71    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X1),X2) | ~r1_tarski(k4_xboole_0(X1,X0),X2) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.79/0.71    inference(cnf_transformation,[],[f28])).
% 2.79/0.71  fof(f28,plain,(
% 2.79/0.71    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X1),X2) | ~r1_tarski(k4_xboole_0(X1,X0),X2) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.79/0.71    inference(flattening,[],[f27])).
% 2.79/0.71  fof(f27,plain,(
% 2.79/0.71    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X1),X2) | (~r1_tarski(k4_xboole_0(X1,X0),X2) | ~r1_tarski(k4_xboole_0(X0,X1),X2)))),
% 2.79/0.71    inference(ennf_transformation,[],[f15])).
% 2.79/0.71  fof(f15,axiom,(
% 2.79/0.71    ! [X0,X1,X2] : ((r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)) => r1_tarski(k5_xboole_0(X0,X1),X2))),
% 2.79/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_xboole_1)).
% 2.79/0.71  fof(f3419,plain,(
% 2.79/0.71    ( ! [X0] : (r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),sK1)) ) | ~spl5_81),
% 2.79/0.71    inference(avatar_component_clause,[],[f3418])).
% 2.79/0.71  fof(f3418,plain,(
% 2.79/0.71    spl5_81 <=> ! [X0] : r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),sK1)),
% 2.79/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).
% 2.79/0.71  fof(f3784,plain,(
% 2.79/0.71    ( ! [X0] : (r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,X0)),sK1)) ) | ~spl5_96),
% 2.79/0.71    inference(avatar_component_clause,[],[f3783])).
% 2.79/0.71  fof(f3783,plain,(
% 2.79/0.71    spl5_96 <=> ! [X0] : r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,X0)),sK1)),
% 2.79/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).
% 2.79/0.71  fof(f37,plain,(
% 2.79/0.71    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1)),
% 2.79/0.71    inference(cnf_transformation,[],[f30])).
% 2.79/0.71  fof(f30,plain,(
% 2.79/0.71    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1)),
% 2.79/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f29])).
% 2.79/0.71  fof(f29,plain,(
% 2.79/0.71    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => (~r1_tarski(k5_xboole_0(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1))),
% 2.79/0.71    introduced(choice_axiom,[])).
% 2.79/0.71  fof(f21,plain,(
% 2.79/0.71    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1))),
% 2.79/0.71    inference(flattening,[],[f20])).
% 2.79/0.71  fof(f20,plain,(
% 2.79/0.71    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & (r1_tarski(X2,X1) & r1_tarski(X0,X1)))),
% 2.79/0.71    inference(ennf_transformation,[],[f18])).
% 2.79/0.71  fof(f18,negated_conjecture,(
% 2.79/0.71    ~! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 2.79/0.71    inference(negated_conjecture,[],[f17])).
% 2.79/0.71  fof(f17,conjecture,(
% 2.79/0.71    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 2.79/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).
% 2.79/0.71  fof(f3785,plain,(
% 2.79/0.71    spl5_96 | ~spl5_91),
% 2.79/0.71    inference(avatar_split_clause,[],[f3734,f3729,f3783])).
% 2.79/0.71  fof(f3729,plain,(
% 2.79/0.71    spl5_91 <=> ! [X2] : (~r1_tarski(X2,sK2) | r1_tarski(X2,sK1))),
% 2.79/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).
% 2.79/0.71  fof(f3734,plain,(
% 2.79/0.71    ( ! [X0] : (r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,X0)),sK1)) ) | ~spl5_91),
% 2.79/0.71    inference(unit_resulting_resolution,[],[f56,f3730])).
% 2.79/0.71  fof(f3730,plain,(
% 2.79/0.71    ( ! [X2] : (~r1_tarski(X2,sK2) | r1_tarski(X2,sK1)) ) | ~spl5_91),
% 2.79/0.71    inference(avatar_component_clause,[],[f3729])).
% 2.79/0.71  fof(f56,plain,(
% 2.79/0.71    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 2.79/0.71    inference(definition_unfolding,[],[f41,f45])).
% 2.79/0.71  fof(f41,plain,(
% 2.79/0.71    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.79/0.71    inference(cnf_transformation,[],[f10])).
% 2.79/0.71  fof(f10,axiom,(
% 2.79/0.71    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.79/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.79/0.71  fof(f3731,plain,(
% 2.79/0.71    spl5_91 | ~spl5_84),
% 2.79/0.71    inference(avatar_split_clause,[],[f3672,f3650,f3729])).
% 2.79/0.71  fof(f3650,plain,(
% 2.79/0.71    spl5_84 <=> sK2 = k3_xboole_0(sK1,sK2)),
% 2.79/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).
% 2.79/0.71  fof(f3672,plain,(
% 2.79/0.71    ( ! [X2] : (~r1_tarski(X2,sK2) | r1_tarski(X2,sK1)) ) | ~spl5_84),
% 2.79/0.71    inference(superposition,[],[f53,f3652])).
% 2.79/0.71  fof(f3652,plain,(
% 2.79/0.71    sK2 = k3_xboole_0(sK1,sK2) | ~spl5_84),
% 2.79/0.71    inference(avatar_component_clause,[],[f3650])).
% 2.79/0.71  fof(f53,plain,(
% 2.79/0.71    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 2.79/0.71    inference(cnf_transformation,[],[f26])).
% 2.79/0.71  fof(f26,plain,(
% 2.79/0.71    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 2.79/0.71    inference(ennf_transformation,[],[f8])).
% 2.79/0.71  fof(f8,axiom,(
% 2.79/0.71    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 2.79/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
% 2.79/0.71  fof(f3700,plain,(
% 2.79/0.71    ~spl5_87 | ~spl5_22 | ~spl5_84),
% 2.79/0.71    inference(avatar_split_clause,[],[f3667,f3650,f473,f3697])).
% 2.79/0.71  fof(f3697,plain,(
% 2.79/0.71    spl5_87 <=> r1_tarski(k5_xboole_0(sK0,sK2),sK2)),
% 2.79/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).
% 2.79/0.71  fof(f473,plain,(
% 2.79/0.71    spl5_22 <=> ! [X0] : ~r1_tarski(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0))),
% 2.79/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 2.79/0.71  fof(f3667,plain,(
% 2.79/0.71    ~r1_tarski(k5_xboole_0(sK0,sK2),sK2) | (~spl5_22 | ~spl5_84)),
% 2.79/0.71    inference(superposition,[],[f474,f3652])).
% 2.79/0.71  fof(f474,plain,(
% 2.79/0.71    ( ! [X0] : (~r1_tarski(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0))) ) | ~spl5_22),
% 2.79/0.71    inference(avatar_component_clause,[],[f473])).
% 2.79/0.71  fof(f3653,plain,(
% 2.79/0.71    spl5_84 | ~spl5_83),
% 2.79/0.71    inference(avatar_split_clause,[],[f3616,f3558,f3650])).
% 2.79/0.71  fof(f3558,plain,(
% 2.79/0.71    spl5_83 <=> k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))),
% 2.79/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).
% 2.79/0.71  fof(f3616,plain,(
% 2.79/0.71    sK2 = k3_xboole_0(sK1,sK2) | ~spl5_83),
% 2.79/0.71    inference(forward_demodulation,[],[f3576,f39])).
% 2.79/0.71  fof(f39,plain,(
% 2.79/0.71    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.79/0.71    inference(cnf_transformation,[],[f11])).
% 2.79/0.71  fof(f11,axiom,(
% 2.79/0.71    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.79/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.79/0.71  fof(f3576,plain,(
% 2.79/0.71    k5_xboole_0(sK2,k1_xboole_0) = k3_xboole_0(sK1,sK2) | ~spl5_83),
% 2.79/0.71    inference(superposition,[],[f1234,f3560])).
% 2.79/0.71  fof(f3560,plain,(
% 2.79/0.71    k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)) | ~spl5_83),
% 2.79/0.71    inference(avatar_component_clause,[],[f3558])).
% 2.79/0.71  fof(f1234,plain,(
% 2.79/0.71    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.79/0.71    inference(forward_demodulation,[],[f1206,f75])).
% 2.79/0.71  fof(f75,plain,(
% 2.79/0.71    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.79/0.71    inference(superposition,[],[f42,f39])).
% 2.79/0.71  fof(f42,plain,(
% 2.79/0.71    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.79/0.71    inference(cnf_transformation,[],[f1])).
% 2.79/0.71  fof(f1,axiom,(
% 2.79/0.71    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.79/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.79/0.71  fof(f1206,plain,(
% 2.79/0.71    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.79/0.71    inference(superposition,[],[f52,f38])).
% 2.79/0.71  fof(f38,plain,(
% 2.79/0.71    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.79/0.71    inference(cnf_transformation,[],[f13])).
% 2.79/0.71  fof(f13,axiom,(
% 2.79/0.71    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.79/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.79/0.71  fof(f52,plain,(
% 2.79/0.71    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.79/0.71    inference(cnf_transformation,[],[f12])).
% 2.79/0.71  fof(f12,axiom,(
% 2.79/0.71    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.79/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.79/0.71  fof(f3561,plain,(
% 2.79/0.71    spl5_83 | ~spl5_61),
% 2.79/0.71    inference(avatar_split_clause,[],[f3530,f3016,f3558])).
% 2.79/0.71  fof(f3016,plain,(
% 2.79/0.71    spl5_61 <=> sK1 = k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 2.79/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).
% 2.79/0.71  fof(f3530,plain,(
% 2.79/0.71    k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)) | ~spl5_61),
% 2.79/0.71    inference(forward_demodulation,[],[f3529,f1234])).
% 2.79/0.71  fof(f3529,plain,(
% 2.79/0.71    k1_xboole_0 = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) | ~spl5_61),
% 2.79/0.71    inference(forward_demodulation,[],[f3495,f42])).
% 2.79/0.71  fof(f3495,plain,(
% 2.79/0.71    k1_xboole_0 = k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)) | ~spl5_61),
% 2.79/0.71    inference(superposition,[],[f1212,f3018])).
% 2.79/0.71  fof(f3018,plain,(
% 2.79/0.71    sK1 = k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl5_61),
% 2.79/0.71    inference(avatar_component_clause,[],[f3016])).
% 2.79/0.71  fof(f1212,plain,(
% 2.79/0.71    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 2.79/0.71    inference(superposition,[],[f52,f38])).
% 2.79/0.71  fof(f3420,plain,(
% 2.79/0.71    spl5_81 | ~spl5_76),
% 2.79/0.71    inference(avatar_split_clause,[],[f3369,f3365,f3418])).
% 2.79/0.71  fof(f3365,plain,(
% 2.79/0.71    spl5_76 <=> ! [X2] : (~r1_tarski(X2,sK0) | r1_tarski(X2,sK1))),
% 2.79/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).
% 2.79/0.71  fof(f3369,plain,(
% 2.79/0.71    ( ! [X0] : (r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),sK1)) ) | ~spl5_76),
% 2.79/0.71    inference(unit_resulting_resolution,[],[f56,f3366])).
% 2.79/0.71  fof(f3366,plain,(
% 2.79/0.71    ( ! [X2] : (r1_tarski(X2,sK1) | ~r1_tarski(X2,sK0)) ) | ~spl5_76),
% 2.79/0.71    inference(avatar_component_clause,[],[f3365])).
% 2.79/0.71  fof(f3367,plain,(
% 2.79/0.71    spl5_76 | ~spl5_63),
% 2.79/0.71    inference(avatar_split_clause,[],[f3204,f3182,f3365])).
% 2.79/0.71  fof(f3182,plain,(
% 2.79/0.71    spl5_63 <=> sK0 = k3_xboole_0(sK1,sK0)),
% 2.79/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).
% 2.79/0.71  fof(f3204,plain,(
% 2.79/0.71    ( ! [X2] : (~r1_tarski(X2,sK0) | r1_tarski(X2,sK1)) ) | ~spl5_63),
% 2.79/0.71    inference(superposition,[],[f53,f3184])).
% 2.79/0.71  fof(f3184,plain,(
% 2.79/0.71    sK0 = k3_xboole_0(sK1,sK0) | ~spl5_63),
% 2.79/0.71    inference(avatar_component_clause,[],[f3182])).
% 2.79/0.71  fof(f3185,plain,(
% 2.79/0.71    spl5_63 | ~spl5_62),
% 2.79/0.71    inference(avatar_split_clause,[],[f3148,f3090,f3182])).
% 2.79/0.71  fof(f3090,plain,(
% 2.79/0.71    spl5_62 <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK1,sK0))),
% 2.79/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).
% 2.79/0.71  fof(f3148,plain,(
% 2.79/0.71    sK0 = k3_xboole_0(sK1,sK0) | ~spl5_62),
% 2.79/0.71    inference(forward_demodulation,[],[f3108,f39])).
% 2.79/0.71  fof(f3108,plain,(
% 2.79/0.71    k5_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK1,sK0) | ~spl5_62),
% 2.79/0.71    inference(superposition,[],[f1234,f3092])).
% 2.79/0.71  fof(f3092,plain,(
% 2.79/0.71    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) | ~spl5_62),
% 2.79/0.71    inference(avatar_component_clause,[],[f3090])).
% 2.79/0.71  fof(f3093,plain,(
% 2.79/0.71    spl5_62 | ~spl5_60),
% 2.79/0.71    inference(avatar_split_clause,[],[f3066,f3011,f3090])).
% 2.79/0.71  fof(f3011,plain,(
% 2.79/0.71    spl5_60 <=> sK1 = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),
% 2.79/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).
% 2.79/0.71  fof(f3066,plain,(
% 2.79/0.71    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) | ~spl5_60),
% 2.79/0.71    inference(forward_demodulation,[],[f3065,f1234])).
% 2.79/0.71  fof(f3065,plain,(
% 2.79/0.71    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))) | ~spl5_60),
% 2.79/0.71    inference(forward_demodulation,[],[f3031,f42])).
% 2.79/0.71  fof(f3031,plain,(
% 2.79/0.71    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)),sK1)) | ~spl5_60),
% 2.79/0.71    inference(superposition,[],[f1212,f3013])).
% 2.79/0.71  fof(f3013,plain,(
% 2.79/0.71    sK1 = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) | ~spl5_60),
% 2.79/0.71    inference(avatar_component_clause,[],[f3011])).
% 2.79/0.71  fof(f3019,plain,(
% 2.79/0.71    spl5_61 | ~spl5_2),
% 2.79/0.71    inference(avatar_split_clause,[],[f2997,f66,f3016])).
% 2.79/0.71  fof(f66,plain,(
% 2.79/0.71    spl5_2 <=> r1_tarski(sK2,sK1)),
% 2.79/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.79/0.71  fof(f2997,plain,(
% 2.79/0.71    sK1 = k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl5_2),
% 2.79/0.71    inference(unit_resulting_resolution,[],[f68,f58])).
% 2.79/0.71  fof(f58,plain,(
% 2.79/0.71    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1) )),
% 2.79/0.71    inference(definition_unfolding,[],[f49,f55])).
% 2.79/0.71  fof(f55,plain,(
% 2.79/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.79/0.71    inference(definition_unfolding,[],[f44,f45])).
% 2.79/0.71  fof(f44,plain,(
% 2.79/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.79/0.71    inference(cnf_transformation,[],[f16])).
% 2.79/0.71  fof(f16,axiom,(
% 2.79/0.71    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.79/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.79/0.71  fof(f49,plain,(
% 2.79/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.79/0.71    inference(cnf_transformation,[],[f24])).
% 2.79/0.71  fof(f24,plain,(
% 2.79/0.71    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.79/0.71    inference(ennf_transformation,[],[f6])).
% 2.79/0.71  fof(f6,axiom,(
% 2.79/0.71    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.79/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.79/0.71  fof(f68,plain,(
% 2.79/0.71    r1_tarski(sK2,sK1) | ~spl5_2),
% 2.79/0.71    inference(avatar_component_clause,[],[f66])).
% 2.79/0.71  fof(f3014,plain,(
% 2.79/0.71    spl5_60 | ~spl5_1),
% 2.79/0.71    inference(avatar_split_clause,[],[f2996,f61,f3011])).
% 2.79/0.71  fof(f61,plain,(
% 2.79/0.71    spl5_1 <=> r1_tarski(sK0,sK1)),
% 2.79/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.79/0.71  fof(f2996,plain,(
% 2.79/0.71    sK1 = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) | ~spl5_1),
% 2.79/0.71    inference(unit_resulting_resolution,[],[f63,f58])).
% 2.79/0.71  fof(f63,plain,(
% 2.79/0.71    r1_tarski(sK0,sK1) | ~spl5_1),
% 2.79/0.71    inference(avatar_component_clause,[],[f61])).
% 2.79/0.71  fof(f475,plain,(
% 2.79/0.71    spl5_22 | spl5_3),
% 2.79/0.71    inference(avatar_split_clause,[],[f405,f71,f473])).
% 2.79/0.71  fof(f71,plain,(
% 2.79/0.71    spl5_3 <=> r1_tarski(k5_xboole_0(sK0,sK2),sK1)),
% 2.79/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.79/0.71  fof(f405,plain,(
% 2.79/0.71    ( ! [X0] : (~r1_tarski(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0))) ) | spl5_3),
% 2.79/0.71    inference(unit_resulting_resolution,[],[f73,f53])).
% 2.79/0.71  fof(f73,plain,(
% 2.79/0.71    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1) | spl5_3),
% 2.79/0.71    inference(avatar_component_clause,[],[f71])).
% 2.79/0.71  fof(f74,plain,(
% 2.79/0.71    ~spl5_3),
% 2.79/0.71    inference(avatar_split_clause,[],[f37,f71])).
% 2.79/0.71  fof(f69,plain,(
% 2.79/0.71    spl5_2),
% 2.79/0.71    inference(avatar_split_clause,[],[f36,f66])).
% 2.79/0.71  fof(f36,plain,(
% 2.79/0.71    r1_tarski(sK2,sK1)),
% 2.79/0.71    inference(cnf_transformation,[],[f30])).
% 2.79/0.71  fof(f64,plain,(
% 2.79/0.71    spl5_1),
% 2.79/0.71    inference(avatar_split_clause,[],[f35,f61])).
% 2.79/0.71  fof(f35,plain,(
% 2.79/0.71    r1_tarski(sK0,sK1)),
% 2.79/0.71    inference(cnf_transformation,[],[f30])).
% 2.79/0.71  % SZS output end Proof for theBenchmark
% 2.79/0.71  % (24267)------------------------------
% 2.79/0.71  % (24267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.79/0.71  % (24267)Termination reason: Refutation
% 2.79/0.71  
% 2.79/0.71  % (24267)Memory used [KB]: 13048
% 2.79/0.71  % (24267)Time elapsed: 0.285 s
% 2.79/0.71  % (24267)------------------------------
% 2.79/0.71  % (24267)------------------------------
% 2.79/0.72  % (24249)Success in time 0.358 s
%------------------------------------------------------------------------------
