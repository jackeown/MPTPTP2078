%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:51 EST 2020

% Result     : Theorem 1.78s
% Output     : Refutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 444 expanded)
%              Number of leaves         :   18 ( 145 expanded)
%              Depth                    :   16
%              Number of atoms          :  194 ( 647 expanded)
%              Number of equality atoms :   30 ( 333 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1027,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f236,f1013,f1025,f1026])).

fof(f1026,plain,
    ( spl2_2
    | ~ spl2_15 ),
    inference(avatar_contradiction_clause,[],[f1019])).

fof(f1019,plain,
    ( $false
    | spl2_2
    | ~ spl2_15 ),
    inference(unit_resulting_resolution,[],[f26,f29,f235,f955,f922])).

fof(f922,plain,(
    ! [X4,X5] :
      ( r1_tarski(k1_relat_1(X4),k1_relat_1(X5))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | ~ r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f412,f54])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f412,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k1_relat_1(X1))
      | r1_tarski(X2,k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f316,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(X1,X1,X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f51,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f30,f44,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f44])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f316,plain,(
    ! [X12,X13,X11] :
      ( r1_tarski(X13,k1_relat_1(k3_tarski(k2_enumset1(X11,X11,X11,X12))))
      | ~ r1_tarski(X13,k1_relat_1(X12))
      | ~ v1_relat_1(X12)
      | ~ v1_relat_1(X11) ) ),
    inference(superposition,[],[f52,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f27,f45,f45])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f45])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f955,plain,
    ( v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f954])).

fof(f954,plain,
    ( spl2_15
  <=> v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f235,plain,
    ( ~ r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK0))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl2_2
  <=> r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

fof(f1025,plain,
    ( spl2_1
    | ~ spl2_15 ),
    inference(avatar_contradiction_clause,[],[f1018])).

fof(f1018,plain,
    ( $false
    | spl2_1
    | ~ spl2_15 ),
    inference(unit_resulting_resolution,[],[f24,f104,f231,f955,f922])).

fof(f231,plain,
    ( ~ r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl2_1
  <=> r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f104,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(forward_demodulation,[],[f97,f50])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f44])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f97,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),X0) ),
    inference(superposition,[],[f29,f77])).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(superposition,[],[f50,f49])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f1013,plain,(
    spl2_15 ),
    inference(avatar_contradiction_clause,[],[f986])).

fof(f986,plain,
    ( $false
    | spl2_15 ),
    inference(unit_resulting_resolution,[],[f24,f54,f956,f585])).

fof(f585,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(X8,k4_xboole_0(X7,k4_xboole_0(X7,X6)))
      | ~ v1_relat_1(X6)
      | v1_relat_1(X8) ) ),
    inference(superposition,[],[f557,f96])).

fof(f96,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(X3,k4_xboole_0(X3,X2)) ),
    inference(superposition,[],[f77,f50])).

fof(f557,plain,(
    ! [X12,X10,X11] :
      ( ~ r1_tarski(X11,k4_xboole_0(X10,X12))
      | ~ v1_relat_1(X10)
      | v1_relat_1(X11) ) ),
    inference(resolution,[],[f542,f54])).

fof(f542,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r1_tarski(X5,k4_xboole_0(X4,X6))
      | ~ v1_relat_1(X4)
      | ~ r1_tarski(X3,X5)
      | v1_relat_1(X3) ) ),
    inference(resolution,[],[f536,f29])).

fof(f536,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X3,X2)
      | v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X3) ) ),
    inference(condensation,[],[f517])).

fof(f517,plain,(
    ! [X12,X10,X13,X11,X9] :
      ( ~ r1_tarski(X9,X10)
      | v1_relat_1(X9)
      | ~ r1_tarski(X9,X11)
      | ~ v1_relat_1(X12)
      | ~ r1_tarski(X13,X12)
      | ~ r1_tarski(X11,X13) ) ),
    inference(resolution,[],[f162,f208])).

fof(f208,plain,(
    ! [X14,X15,X13,X16] :
      ( v1_relat_1(k4_xboole_0(X13,X14))
      | ~ v1_relat_1(X15)
      | ~ r1_tarski(X16,X15)
      | ~ r1_tarski(X13,X16) ) ),
    inference(resolution,[],[f201,f75])).

fof(f75,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k4_xboole_0(X2,X3),X4)
      | ~ r1_tarski(X2,X4) ) ),
    inference(resolution,[],[f72,f29])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | r1_tarski(X2,X0)
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f52,f62])).

fof(f201,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f65,f62])).

fof(f65,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_relat_1(k3_tarski(k2_enumset1(X5,X5,X5,X4)))
      | v1_relat_1(X3)
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f52,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f28,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f162,plain,(
    ! [X10,X11,X9] :
      ( ~ v1_relat_1(k4_xboole_0(X10,k4_xboole_0(X10,X11)))
      | ~ r1_tarski(X9,X11)
      | v1_relat_1(X9)
      | ~ r1_tarski(X9,X10) ) ),
    inference(resolution,[],[f111,f57])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2) ) ),
    inference(forward_demodulation,[],[f53,f50])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f43,f46])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f956,plain,
    ( ~ v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_15 ),
    inference(avatar_component_clause,[],[f954])).

fof(f236,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f227,f233,f229])).

fof(f227,plain,
    ( ~ r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK0))
    | ~ r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK1)) ),
    inference(resolution,[],[f198,f111])).

fof(f198,plain,(
    ~ r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))) ),
    inference(forward_demodulation,[],[f197,f50])).

fof(f197,plain,(
    ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))) ),
    inference(forward_demodulation,[],[f47,f50])).

fof(f47,plain,(
    ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f25,f46,f46])).

fof(f25,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:32:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (10531)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.49  % (10523)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.50  % (10514)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (10515)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (10537)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.51  % (10511)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (10512)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (10520)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (10510)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (10535)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (10535)Refutation not found, incomplete strategy% (10535)------------------------------
% 0.20/0.52  % (10535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10509)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (10523)Refutation not found, incomplete strategy% (10523)------------------------------
% 0.20/0.52  % (10523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10528)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.52  % (10523)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (10523)Memory used [KB]: 1918
% 0.20/0.52  % (10523)Time elapsed: 0.075 s
% 0.20/0.52  % (10523)------------------------------
% 0.20/0.52  % (10523)------------------------------
% 0.20/0.53  % (10536)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (10518)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.53  % (10513)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (10510)Refutation not found, incomplete strategy% (10510)------------------------------
% 0.20/0.53  % (10510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (10510)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (10510)Memory used [KB]: 1791
% 0.20/0.53  % (10510)Time elapsed: 0.116 s
% 0.20/0.53  % (10510)------------------------------
% 0.20/0.53  % (10510)------------------------------
% 0.20/0.53  % (10527)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.53  % (10519)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  % (10525)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (10537)Refutation not found, incomplete strategy% (10537)------------------------------
% 0.20/0.53  % (10537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (10537)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (10537)Memory used [KB]: 10618
% 0.20/0.53  % (10537)Time elapsed: 0.131 s
% 0.20/0.53  % (10537)------------------------------
% 0.20/0.53  % (10537)------------------------------
% 0.20/0.53  % (10525)Refutation not found, incomplete strategy% (10525)------------------------------
% 0.20/0.53  % (10525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (10525)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (10525)Memory used [KB]: 10618
% 0.20/0.53  % (10525)Time elapsed: 0.130 s
% 0.20/0.53  % (10525)------------------------------
% 0.20/0.53  % (10525)------------------------------
% 0.20/0.53  % (10535)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (10535)Memory used [KB]: 6268
% 0.20/0.53  % (10535)Time elapsed: 0.095 s
% 0.20/0.53  % (10535)------------------------------
% 0.20/0.53  % (10535)------------------------------
% 0.20/0.53  % (10532)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (10538)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (10538)Refutation not found, incomplete strategy% (10538)------------------------------
% 0.20/0.54  % (10538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (10517)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (10533)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (10529)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (10524)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (10530)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (10522)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (10516)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (10533)Refutation not found, incomplete strategy% (10533)------------------------------
% 0.20/0.54  % (10533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (10538)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (10538)Memory used [KB]: 1663
% 0.20/0.54  % (10538)Time elapsed: 0.131 s
% 0.20/0.54  % (10538)------------------------------
% 0.20/0.54  % (10538)------------------------------
% 0.20/0.55  % (10519)Refutation not found, incomplete strategy% (10519)------------------------------
% 0.20/0.55  % (10519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (10519)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (10519)Memory used [KB]: 10618
% 0.20/0.55  % (10519)Time elapsed: 0.149 s
% 0.20/0.55  % (10519)------------------------------
% 0.20/0.55  % (10519)------------------------------
% 0.20/0.56  % (10533)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (10533)Memory used [KB]: 10746
% 0.20/0.56  % (10533)Time elapsed: 0.131 s
% 0.20/0.56  % (10533)------------------------------
% 0.20/0.56  % (10533)------------------------------
% 0.20/0.57  % (10521)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.58  % (10534)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.59  % (10526)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.78/0.62  % (10522)Refutation found. Thanks to Tanya!
% 1.78/0.62  % SZS status Theorem for theBenchmark
% 1.78/0.62  % SZS output start Proof for theBenchmark
% 1.78/0.62  fof(f1027,plain,(
% 1.78/0.62    $false),
% 1.78/0.62    inference(avatar_sat_refutation,[],[f236,f1013,f1025,f1026])).
% 1.78/0.62  fof(f1026,plain,(
% 1.78/0.62    spl2_2 | ~spl2_15),
% 1.78/0.62    inference(avatar_contradiction_clause,[],[f1019])).
% 1.78/0.62  fof(f1019,plain,(
% 1.78/0.62    $false | (spl2_2 | ~spl2_15)),
% 1.78/0.62    inference(unit_resulting_resolution,[],[f26,f29,f235,f955,f922])).
% 1.78/0.62  fof(f922,plain,(
% 1.78/0.62    ( ! [X4,X5] : (r1_tarski(k1_relat_1(X4),k1_relat_1(X5)) | ~v1_relat_1(X4) | ~v1_relat_1(X5) | ~r1_tarski(X4,X5)) )),
% 1.78/0.62    inference(resolution,[],[f412,f54])).
% 1.78/0.62  fof(f54,plain,(
% 1.78/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.78/0.62    inference(equality_resolution,[],[f37])).
% 1.78/0.62  fof(f37,plain,(
% 1.78/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.78/0.62    inference(cnf_transformation,[],[f1])).
% 1.78/0.62  fof(f1,axiom,(
% 1.78/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.78/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.78/0.62  fof(f412,plain,(
% 1.78/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X2,k1_relat_1(X1)) | r1_tarski(X2,k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r1_tarski(X1,X0)) )),
% 1.78/0.62    inference(superposition,[],[f316,f62])).
% 1.78/0.62  fof(f62,plain,(
% 1.78/0.62    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X1,X1,X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.78/0.62    inference(superposition,[],[f51,f49])).
% 1.78/0.62  fof(f49,plain,(
% 1.78/0.62    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 1.78/0.62    inference(definition_unfolding,[],[f30,f44,f44])).
% 1.78/0.62  fof(f44,plain,(
% 1.78/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.78/0.62    inference(definition_unfolding,[],[f33,f41])).
% 1.78/0.62  fof(f41,plain,(
% 1.78/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.78/0.62    inference(cnf_transformation,[],[f9])).
% 1.78/0.62  fof(f9,axiom,(
% 1.78/0.62    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.78/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.78/0.62  fof(f33,plain,(
% 1.78/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.78/0.62    inference(cnf_transformation,[],[f8])).
% 1.78/0.62  fof(f8,axiom,(
% 1.78/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.78/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.78/0.62  fof(f30,plain,(
% 1.78/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.78/0.62    inference(cnf_transformation,[],[f7])).
% 1.78/0.62  fof(f7,axiom,(
% 1.78/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.78/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.78/0.62  fof(f51,plain,(
% 1.78/0.62    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.78/0.62    inference(definition_unfolding,[],[f35,f45])).
% 1.78/0.62  fof(f45,plain,(
% 1.78/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.78/0.62    inference(definition_unfolding,[],[f32,f44])).
% 1.78/0.62  fof(f32,plain,(
% 1.78/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.78/0.62    inference(cnf_transformation,[],[f10])).
% 1.78/0.62  fof(f10,axiom,(
% 1.78/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.78/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.78/0.62  fof(f35,plain,(
% 1.78/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.78/0.62    inference(cnf_transformation,[],[f20])).
% 1.78/0.62  fof(f20,plain,(
% 1.78/0.62    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.78/0.62    inference(ennf_transformation,[],[f3])).
% 1.78/0.62  fof(f3,axiom,(
% 1.78/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.78/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.78/0.62  fof(f316,plain,(
% 1.78/0.62    ( ! [X12,X13,X11] : (r1_tarski(X13,k1_relat_1(k3_tarski(k2_enumset1(X11,X11,X11,X12)))) | ~r1_tarski(X13,k1_relat_1(X12)) | ~v1_relat_1(X12) | ~v1_relat_1(X11)) )),
% 1.78/0.62    inference(superposition,[],[f52,f48])).
% 1.78/0.62  fof(f48,plain,(
% 1.78/0.62    ( ! [X0,X1] : (k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.78/0.62    inference(definition_unfolding,[],[f27,f45,f45])).
% 1.78/0.62  fof(f27,plain,(
% 1.78/0.62    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) )),
% 1.78/0.62    inference(cnf_transformation,[],[f18])).
% 1.78/0.62  fof(f18,plain,(
% 1.78/0.62    ! [X0] : (! [X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.78/0.62    inference(ennf_transformation,[],[f14])).
% 1.78/0.62  fof(f14,axiom,(
% 1.78/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))))),
% 1.78/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).
% 1.78/0.62  fof(f52,plain,(
% 1.78/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 1.78/0.62    inference(definition_unfolding,[],[f42,f45])).
% 1.78/0.62  fof(f42,plain,(
% 1.78/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 1.78/0.62    inference(cnf_transformation,[],[f21])).
% 1.78/0.62  fof(f21,plain,(
% 1.78/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.78/0.62    inference(ennf_transformation,[],[f2])).
% 1.78/0.62  fof(f2,axiom,(
% 1.78/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.78/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.78/0.62  fof(f955,plain,(
% 1.78/0.62    v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl2_15),
% 1.78/0.62    inference(avatar_component_clause,[],[f954])).
% 1.78/0.62  fof(f954,plain,(
% 1.78/0.62    spl2_15 <=> v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.78/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 1.78/0.62  fof(f235,plain,(
% 1.78/0.62    ~r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK0)) | spl2_2),
% 1.78/0.62    inference(avatar_component_clause,[],[f233])).
% 1.78/0.62  fof(f233,plain,(
% 1.78/0.62    spl2_2 <=> r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK0))),
% 1.78/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.78/0.62  fof(f29,plain,(
% 1.78/0.62    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.78/0.62    inference(cnf_transformation,[],[f5])).
% 1.78/0.62  fof(f5,axiom,(
% 1.78/0.62    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.78/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.78/0.62  fof(f26,plain,(
% 1.78/0.62    v1_relat_1(sK0)),
% 1.78/0.62    inference(cnf_transformation,[],[f17])).
% 1.78/0.62  fof(f17,plain,(
% 1.78/0.62    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.78/0.62    inference(ennf_transformation,[],[f16])).
% 1.78/0.62  fof(f16,negated_conjecture,(
% 1.78/0.62    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 1.78/0.62    inference(negated_conjecture,[],[f15])).
% 1.78/0.62  fof(f15,conjecture,(
% 1.78/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 1.78/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).
% 1.78/0.62  fof(f1025,plain,(
% 1.78/0.62    spl2_1 | ~spl2_15),
% 1.78/0.62    inference(avatar_contradiction_clause,[],[f1018])).
% 1.78/0.62  fof(f1018,plain,(
% 1.78/0.62    $false | (spl2_1 | ~spl2_15)),
% 1.78/0.62    inference(unit_resulting_resolution,[],[f24,f104,f231,f955,f922])).
% 1.78/0.62  fof(f231,plain,(
% 1.78/0.62    ~r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK1)) | spl2_1),
% 1.78/0.62    inference(avatar_component_clause,[],[f229])).
% 1.78/0.62  fof(f229,plain,(
% 1.78/0.62    spl2_1 <=> r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK1))),
% 1.78/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.78/0.62  fof(f104,plain,(
% 1.78/0.62    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) )),
% 1.78/0.62    inference(forward_demodulation,[],[f97,f50])).
% 1.78/0.62  fof(f50,plain,(
% 1.78/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.78/0.62    inference(definition_unfolding,[],[f34,f46])).
% 1.78/0.62  fof(f46,plain,(
% 1.78/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.78/0.62    inference(definition_unfolding,[],[f31,f44])).
% 1.78/0.62  fof(f31,plain,(
% 1.78/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.78/0.62    inference(cnf_transformation,[],[f11])).
% 1.78/0.62  fof(f11,axiom,(
% 1.78/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.78/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.78/0.62  fof(f34,plain,(
% 1.78/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.78/0.62    inference(cnf_transformation,[],[f6])).
% 1.78/0.62  fof(f6,axiom,(
% 1.78/0.62    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.78/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.78/0.62  fof(f97,plain,(
% 1.78/0.62    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),X0)) )),
% 1.78/0.62    inference(superposition,[],[f29,f77])).
% 1.78/0.62  fof(f77,plain,(
% 1.78/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) )),
% 1.78/0.62    inference(superposition,[],[f50,f49])).
% 1.78/0.62  fof(f24,plain,(
% 1.78/0.62    v1_relat_1(sK1)),
% 1.78/0.62    inference(cnf_transformation,[],[f17])).
% 1.78/0.62  fof(f1013,plain,(
% 1.78/0.62    spl2_15),
% 1.78/0.62    inference(avatar_contradiction_clause,[],[f986])).
% 1.78/0.62  fof(f986,plain,(
% 1.78/0.62    $false | spl2_15),
% 1.78/0.62    inference(unit_resulting_resolution,[],[f24,f54,f956,f585])).
% 1.78/0.62  fof(f585,plain,(
% 1.78/0.62    ( ! [X6,X8,X7] : (~r1_tarski(X8,k4_xboole_0(X7,k4_xboole_0(X7,X6))) | ~v1_relat_1(X6) | v1_relat_1(X8)) )),
% 1.78/0.62    inference(superposition,[],[f557,f96])).
% 1.78/0.62  fof(f96,plain,(
% 1.78/0.62    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(X3,k4_xboole_0(X3,X2))) )),
% 1.78/0.62    inference(superposition,[],[f77,f50])).
% 1.78/0.62  fof(f557,plain,(
% 1.78/0.62    ( ! [X12,X10,X11] : (~r1_tarski(X11,k4_xboole_0(X10,X12)) | ~v1_relat_1(X10) | v1_relat_1(X11)) )),
% 1.78/0.62    inference(resolution,[],[f542,f54])).
% 1.78/0.62  fof(f542,plain,(
% 1.78/0.62    ( ! [X6,X4,X5,X3] : (~r1_tarski(X5,k4_xboole_0(X4,X6)) | ~v1_relat_1(X4) | ~r1_tarski(X3,X5) | v1_relat_1(X3)) )),
% 1.78/0.62    inference(resolution,[],[f536,f29])).
% 1.78/0.62  fof(f536,plain,(
% 1.78/0.62    ( ! [X2,X0,X3,X1] : (~r1_tarski(X3,X2) | v1_relat_1(X0) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1) | ~r1_tarski(X1,X3)) )),
% 1.78/0.62    inference(condensation,[],[f517])).
% 1.78/0.62  fof(f517,plain,(
% 1.78/0.62    ( ! [X12,X10,X13,X11,X9] : (~r1_tarski(X9,X10) | v1_relat_1(X9) | ~r1_tarski(X9,X11) | ~v1_relat_1(X12) | ~r1_tarski(X13,X12) | ~r1_tarski(X11,X13)) )),
% 1.78/0.62    inference(resolution,[],[f162,f208])).
% 1.78/0.62  fof(f208,plain,(
% 1.78/0.62    ( ! [X14,X15,X13,X16] : (v1_relat_1(k4_xboole_0(X13,X14)) | ~v1_relat_1(X15) | ~r1_tarski(X16,X15) | ~r1_tarski(X13,X16)) )),
% 1.78/0.62    inference(resolution,[],[f201,f75])).
% 1.78/0.62  fof(f75,plain,(
% 1.78/0.62    ( ! [X4,X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),X4) | ~r1_tarski(X2,X4)) )),
% 1.78/0.62    inference(resolution,[],[f72,f29])).
% 1.78/0.62  fof(f72,plain,(
% 1.78/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | r1_tarski(X2,X0) | ~r1_tarski(X1,X0)) )),
% 1.78/0.62    inference(superposition,[],[f52,f62])).
% 1.78/0.62  fof(f201,plain,(
% 1.78/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | v1_relat_1(X2) | ~v1_relat_1(X0) | ~r1_tarski(X1,X0)) )),
% 1.78/0.62    inference(superposition,[],[f65,f62])).
% 1.78/0.62  fof(f65,plain,(
% 1.78/0.62    ( ! [X4,X5,X3] : (~v1_relat_1(k3_tarski(k2_enumset1(X5,X5,X5,X4))) | v1_relat_1(X3) | ~r1_tarski(X3,X4)) )),
% 1.78/0.62    inference(resolution,[],[f52,f57])).
% 1.78/0.62  fof(f57,plain,(
% 1.78/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.78/0.62    inference(resolution,[],[f28,f39])).
% 1.78/0.62  fof(f39,plain,(
% 1.78/0.62    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.78/0.62    inference(cnf_transformation,[],[f12])).
% 1.78/0.62  fof(f12,axiom,(
% 1.78/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.78/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.78/0.62  fof(f28,plain,(
% 1.78/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.78/0.62    inference(cnf_transformation,[],[f19])).
% 1.78/0.62  fof(f19,plain,(
% 1.78/0.62    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.78/0.62    inference(ennf_transformation,[],[f13])).
% 1.78/0.62  fof(f13,axiom,(
% 1.78/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.78/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.78/0.62  fof(f162,plain,(
% 1.78/0.62    ( ! [X10,X11,X9] : (~v1_relat_1(k4_xboole_0(X10,k4_xboole_0(X10,X11))) | ~r1_tarski(X9,X11) | v1_relat_1(X9) | ~r1_tarski(X9,X10)) )),
% 1.78/0.62    inference(resolution,[],[f111,f57])).
% 1.78/0.62  fof(f111,plain,(
% 1.78/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X1) | ~r1_tarski(X0,X2)) )),
% 1.78/0.62    inference(forward_demodulation,[],[f53,f50])).
% 1.78/0.62  fof(f53,plain,(
% 1.78/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) )),
% 1.78/0.62    inference(definition_unfolding,[],[f43,f46])).
% 1.78/0.62  fof(f43,plain,(
% 1.78/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 1.78/0.62    inference(cnf_transformation,[],[f23])).
% 1.78/0.62  fof(f23,plain,(
% 1.78/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.78/0.62    inference(flattening,[],[f22])).
% 1.78/0.62  fof(f22,plain,(
% 1.78/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.78/0.62    inference(ennf_transformation,[],[f4])).
% 1.78/0.62  fof(f4,axiom,(
% 1.78/0.62    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.78/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.78/0.62  fof(f956,plain,(
% 1.78/0.62    ~v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_15),
% 1.78/0.62    inference(avatar_component_clause,[],[f954])).
% 1.78/0.62  fof(f236,plain,(
% 1.78/0.62    ~spl2_1 | ~spl2_2),
% 1.78/0.62    inference(avatar_split_clause,[],[f227,f233,f229])).
% 1.78/0.62  fof(f227,plain,(
% 1.78/0.62    ~r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK0)) | ~r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_relat_1(sK1))),
% 1.78/0.62    inference(resolution,[],[f198,f111])).
% 1.78/0.62  fof(f198,plain,(
% 1.78/0.62    ~r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))))),
% 1.78/0.62    inference(forward_demodulation,[],[f197,f50])).
% 1.78/0.62  fof(f197,plain,(
% 1.78/0.62    ~r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))))),
% 1.78/0.62    inference(forward_demodulation,[],[f47,f50])).
% 1.78/0.62  fof(f47,plain,(
% 1.78/0.62    ~r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))))),
% 1.78/0.62    inference(definition_unfolding,[],[f25,f46,f46])).
% 1.78/0.62  fof(f25,plain,(
% 1.78/0.62    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),
% 1.78/0.62    inference(cnf_transformation,[],[f17])).
% 1.78/0.62  % SZS output end Proof for theBenchmark
% 1.78/0.62  % (10522)------------------------------
% 1.78/0.62  % (10522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.62  % (10522)Termination reason: Refutation
% 1.78/0.62  
% 1.78/0.62  % (10522)Memory used [KB]: 6908
% 1.78/0.62  % (10522)Time elapsed: 0.207 s
% 1.78/0.62  % (10522)------------------------------
% 1.78/0.62  % (10522)------------------------------
% 1.78/0.63  % (10507)Success in time 0.268 s
%------------------------------------------------------------------------------
